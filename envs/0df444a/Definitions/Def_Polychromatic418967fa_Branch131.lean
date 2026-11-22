-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch131
-- name    : Polychromatic418967fa_Branch131
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:13:12.512112+00:00
-- url     : https://prove2.me/theorems/84eacd35-d225-4c88-bfb6-5d192c835a36
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

def Polychromatic418967fa.branch_131 : allB 131 131 :=
  allB_succ' 2 130 131 (Eq.refl Bool.true) (allA_of_3_0 2 130 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  129 131 (Eq.refl Bool.true) (allA_succ_of_accept 2 129 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 131 (accept_3_2 1 129 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129 131))) (allB_succ' 4 128 131 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 128 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 131 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 128 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 131 (accept_3_2 1 128 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128 131)))) (allB_succ' 5 127 131 (Eq.refl Bool.true) (allA_of_3_0
  5 127 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 126 131 (Eq.refl Bool.true) (allA_succ_of_accept 5
  126 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 126 131 (accept_3_2 4 126 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 126 131 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 126 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 131 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 126 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 131 (accept_3_2 1 126 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 131)))))) (allB_succ' 7 125 131 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 125 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 131 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 125 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 131 (accept_3_2 4 125 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 3
  125 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 131 (accept_3_2 1 125 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125 131)))))))
  (allB_succ' 8 124 131 (Eq.refl Bool.true) (allA_of_3_0 8 124 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 123 131 (Eq.refl Bool.true) (allA_succ_of_accept 8 123 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 131 (accept_3_2 7 123 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 6
  123 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 131
  (Polychromatic418967fa.accept_13_5_6_1_1_822 5 123 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 131 (accept_3_2 4 123 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 123 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 123 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 131 (accept_3_2 1 123 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 131))))))))) (allB_succ' 10 122 131 (Eq.refl Bool.true) (allA_succ_of_accept 9 122
  131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 122 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 122 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 131 (accept_3_2 7 122 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 122 131 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 122 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 122 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  122 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 131 (accept_3_2 4 122
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 131 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 122 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 131
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 122 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 131 (accept_3_2 1 122 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  131)))))))))) (allB_succ' 11 121 131 (Eq.refl Bool.true) (allA_of_3_0 11 121 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 120 131 (Eq.refl Bool.true) (allA_succ_of_accept 11 120 131
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 120 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 131 (accept_3_2 10 120 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  120 131 (Polychromatic418967fa.accept_18_9_12_5_1_864 9 120 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 120 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 120 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 131 (accept_3_2 7 120 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 120 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 131
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 120 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 120 131 (accept_3_2 4 120 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  120 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 120 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 120 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 120 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 131 (accept_3_2 1 120 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 120 131)))))))))))) (allB_succ' 13 119 131 (Eq.refl Bool.true) (allA_succ_of_accept 12
  119 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 119 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 131 (Polychromatic418967fa.accept_16_11_7_3_1_3163 11 119 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 131 (accept_3_2 10 119 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 131 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 119 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 131 (accept_3_2 7 119 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 119 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 131 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 119 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 131 (accept_3_2 4 119 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 119 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 131
  (Polychromatic418967fa.accept_10_2_9_1_1_185 2 119 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 131 (accept_3_2 1 119 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  131))))))))))))) (allB_succ' 14 118 131 (Eq.refl Bool.true) (allA_of_3_0 14 118 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 117 131 (Eq.refl Bool.true) (allA_succ_of_accept 14 117 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 131 (accept_3_2 13 117 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 131 (Polychromatic418967fa.accept_18_12_9_5_1_2771 12 117 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 131 (Polychromatic418967fa.accept_21_11_12_5_1_2224 11 117 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 131 (accept_3_2 10 117 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 131 (Polychromatic418967fa.accept_21_9_12_5_1_317 9 117 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 131 (accept_3_2 7 117 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 131 (Polychromatic418967fa.accept_19_5_3_17_1_6557 5 117 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 131 (accept_3_2 4 117 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 131 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 117 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 131 (accept_3_2 1 117 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  131))))))))))))))) (allB_succ' 16 116 131 (Eq.refl Bool.true) (allA_succ_of_accept 15 116 131
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 116 131 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 116 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 131 (accept_3_2 13 116 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 116 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 116 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 131 (Polychromatic418967fa.accept_9_2_8_5_1_228
  11 116 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 131 (accept_3_2 10
  116 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 131
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 116 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 116 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 131 (accept_3_2 7 116 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 116 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 116 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 131 (Polychromatic418967fa.accept_10_5_6_1_1_836 5
  116 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 131 (accept_3_2 4 116
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 131 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 116 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 131
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 116 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 131 (accept_3_2 1 116 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  131)))))))))))))))) (allB_succ' 17 115 131 (Eq.refl Bool.true) (allA_of_3_0 17 115 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 114 131 (Eq.refl Bool.true) (allA_succ_of_accept 17 114 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 131 (accept_3_2 16 114 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 114 131 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 114 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 114 131 (Polychromatic418967fa.accept_21_14_9_5_1_6616 14 114 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 131 (accept_3_2 13 114 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 114 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 131
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 114 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 114 131 (accept_3_2 10 114 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  114 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 114 131 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 114 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 131 (accept_3_2 7 114 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 131 (Polychromatic418967fa.accept_15_6_9_11_1_858 6 114 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 131 (accept_3_2 4 114 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  114 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 114 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 114 131 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 114 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 131 (accept_3_2 1 114 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 114 131)))))))))))))))))) (allB_succ' 19 113 131 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 113 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 113 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 131 (accept_3_2 16 113 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 131 (Polychromatic418967fa.accept_13_2_9_1_1_67
  15 113 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 131 (accept_3_2 13 113 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 131 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 113 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 113 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 131 (accept_3_2 10 113 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 131 (Polychromatic418967fa.accept_24_9_17_11_1_4810 9 113 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 131
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 113 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 131 (accept_3_2 7 113 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 131 (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 113 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 131 (accept_3_2 4 113 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 113 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 131 (accept_3_2 1 113 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  131))))))))))))))))))) (allB_succ' 20 112 131 (Eq.refl Bool.true) (allA_of_3_0 20 112 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 111 131 (Eq.refl Bool.true) (allA_succ_of_accept 20 111 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 131 (accept_3_2 19 111 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 111 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 111 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 131 (accept_3_2 16 111 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 111 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 111 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 131 (accept_3_2 13 111 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 111 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 111 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 131 (accept_3_2 10 111 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 131 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 111 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 131 (accept_3_2 7 111 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 111 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 131 (Polychromatic418967fa.accept_15_5_6_11_1_854 5 111 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 131 (accept_3_2 4 111 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 131 (Polychromatic418967fa.accept_13_3_7_1_1_334 3 111 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 111 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 131 (accept_3_2 1 111 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  131))))))))))))))))))))) (allB_succ' 22 110 131 (Eq.refl Bool.true) (allA_succ_of_accept 21 110 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 110 131 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 110 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 131 (accept_3_2 19 110 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 110 131 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 110 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 131 (accept_3_2 16 110 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 110 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 110 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 110 131 (Polychromatic418967fa.accept_19_14_15_17_1_3877 14 110 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 131 (accept_3_2 13 110 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 110 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 131
  (Polychromatic418967fa.accept_16_11_14_3_1_3140 11 110 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 110 131 (accept_3_2 10 110 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 110 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 110 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 131 (accept_3_2 7 110 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  110 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 131 (accept_3_2 4 110 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 110 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 131 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 110 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 131 (accept_3_2 1 110 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110 131)))))))))))))))))))))) (allB_succ' 23 109 131 (Eq.refl Bool.true) (allA_of_3_0
  23 109 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 108 131 (Eq.refl Bool.true) (allA_succ_of_accept 23
  108 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 108 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 108 131 (accept_3_2 22 108 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 108 131 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 108 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 131 (Polychromatic418967fa.accept_16_4_12_3_1_2180 20 108
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 131 (accept_3_2 19 108
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 131
  (Polychromatic418967fa.accept_13_5_4_1_1_364 18 108 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 108 131 (Polychromatic418967fa.accept_20_17_8_11_1_6615 17 108 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 131 (accept_3_2 16 108 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 108 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 131
  (Polychromatic418967fa.accept_15_14_3_11_1_850 14 108 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 131 (accept_3_2 13 108 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 108 131 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 108 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 108 131 (Polychromatic418967fa.accept_17_11_6_12_1_5348 11 108 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 131 (accept_3_2 10 108 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 108 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 131
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 108 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 108 131 (accept_3_2 7 108 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  108 131 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 108 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 108 131 (Polychromatic418967fa.accept_13_5_4_1_1_364 5 108 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 131 (accept_3_2 4 108 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 131 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 108 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 131
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 108 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 131 (accept_3_2 1 108 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  131)))))))))))))))))))))))) (allB_succ' 25 107 131 (Eq.refl Bool.true) (allA_succ_of_accept 24 107 131
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 107 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 107 131 (Polychromatic418967fa.accept_16_7_11_3_1_1330 23 107 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 131 (accept_3_2 22 107 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 107 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 107 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 131 (Polychromatic418967fa.accept_9_2_8_5_1_228
  20 107 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 131 (accept_3_2 19
  107 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 131
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 107 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 107 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 107 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 131 (accept_3_2 16 107 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 107 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 107 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 131 (Polychromatic418967fa.accept_10_4_7_1_1_471
  14 107 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 131 (accept_3_2 13
  107 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 131
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 107 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 107 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 107 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 131 (accept_3_2 10 107 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 107 131 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 107 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 131 (Polychromatic418967fa.accept_16_8_11_3_1_4279
  8 107 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 131 (accept_3_2 7
  107 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 131
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 107 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 107 131 (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 107 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 131 (accept_3_2 4 107 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 107 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 107 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  107 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 131 (accept_3_2 1 107
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107 131))))))))))))))))))))))))) (allB_succ' 26 106 131
  (Eq.refl Bool.true) (allA_of_3_0 26 106 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 105 131 (Eq.refl
  Bool.true) (allA_succ_of_accept 26 105 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 131 (accept_3_2 25 105 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 131 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 105 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 131
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 105 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 131 (accept_3_2 22 105 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 105 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 131 (accept_3_2 19 105 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 105 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 131 (accept_3_2 16 105 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 131 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 105 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 131 (accept_3_2 13 105 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 105 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 131
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 105 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 131 (accept_3_2 10 105 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 131 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 105 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 131 (accept_3_2 7 105 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 131
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 105 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 131 (accept_3_2 4 105 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 131 (accept_3_2 1 105 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105 131))))))))))))))))))))))))))) (allB_succ' 28 104 131 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 104 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 131 (Polychromatic418967fa.accept_11_4_5_10_1_926 26 104
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 131 (accept_3_2 25 104
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 131
  (Polychromatic418967fa.accept_17_7_2_12_1_1069 24 104 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 104 131 (Polychromatic418967fa.accept_17_6_2_12_1_1992 23 104 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 131 (accept_3_2 22 104 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 104 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 131 (Polychromatic418967fa.accept_16_4_8_3_1_4206
  20 104 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 131 (accept_3_2 19
  104 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 131
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 104 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 104 131 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 104 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 131 (accept_3_2 16 104 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 104 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 131 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 104 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 131 (accept_3_2 13
  104 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 131
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 12 104 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 104 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 131 (accept_3_2 10 104 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 131
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 104 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 131 (accept_3_2 7 104 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 131 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 104 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 131 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 104 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 131 (accept_3_2 4 104 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 104 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 131 (accept_3_2 1 104 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  131)))))))))))))))))))))))))))) (allB_succ' 29 103 131 (Eq.refl Bool.true) (allA_of_3_0 29 103 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 102 131 (Eq.refl Bool.true) (allA_succ_of_accept 29 102 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 131 (accept_3_2 28 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 102 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 102 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 102 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 131 (accept_3_2 25 102 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 102 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 131
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 131 (accept_3_2 22 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 102 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 102 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 102 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 131 (accept_3_2 19 102 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 131 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 102 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 131 (accept_3_2 16 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 102 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 102 131 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 102 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 131 (accept_3_2 13 102 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 131 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 102
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 131
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 131 (accept_3_2 10 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 102 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 131 (accept_3_2 7 102 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 102 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 131 (accept_3_2 4 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 131 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 102 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 102 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 131 (accept_3_2 1 102 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 102 131)))))))))))))))))))))))))))))) (allB_succ' 31 101 131 (Eq.refl Bool.true)
  (allA_succ_of_accept 30 101 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 101 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 131 (accept_3_2 28 101 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 131
  (Polychromatic418967fa.accept_19_8_6_17_1_5186 27 101 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 101 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 131 (accept_3_2 25 101 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 101 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 23
  101 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 131 (accept_3_2 22
  101 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 131
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 101 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 101 131 (Polychromatic418967fa.accept_22_20_13_21_1_6614 20 101 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 131 (accept_3_2 19 101 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 101 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 131 (accept_3_2 16 101 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 101 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 131 (accept_3_2 13 101 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 101 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 131
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 101 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 131 (accept_3_2 10 101 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 101 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 101 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 131 (accept_3_2 7 101 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  101 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 131
  (Polychromatic418967fa.accept_23_5_9_16_1_6613 5 101 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 131 (accept_3_2 4 101 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 101 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 131 (accept_3_2 1 101 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 131))))))))))))))))))))))))))))))) (allB_succ' 32 100 131 (Eq.refl Bool.true)
  (allA_of_3_0 32 100 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 99 131 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 131 (accept_3_2 31 99 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 131 (Polychromatic418967fa.accept_18_12_9_5_1_2771 30 99 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 131
  (Polychromatic418967fa.accept_19_10_4_17_1_1544 29 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 131 (accept_3_2 28 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 99 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 131 (accept_3_2 25 99 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 99 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 131
  (Polychromatic418967fa.accept_22_1_11_21_1_6612 23 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 131 (accept_3_2 22 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 131 (accept_3_2 19 99 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 99 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 131
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 131 (accept_3_2 16 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 131 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 99 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 131 (accept_3_2 13 99 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 131 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 99 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 131
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 131 (accept_3_2 10 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 131 (accept_3_2 7 99 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 99 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 131
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 131 (accept_3_2 4 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  131 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 99 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 131 (accept_3_2 1 99 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 131))))))))))))))))))))))))))))))))) (allB_succ' 34 98 131 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 98 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 131 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 98 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 98 131 (accept_3_2 31 98 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 98 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 30
  98 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 98 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 98 131 (accept_3_2 28 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  98 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 98 131 (Polychromatic418967fa.accept_25_1_23_6_1_6611 26 98 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 98 131 (accept_3_2 25 98 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 98 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 98 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 98 131
  (Polychromatic418967fa.accept_10_3_8_1_1_182 23 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 98 131 (accept_3_2 22 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  98 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 98 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 98 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 98 131 (accept_3_2 19 98 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 98 131 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 98 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 98 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 98 131 (accept_3_2 16 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  98 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 98 131 (Polychromatic418967fa.accept_18_14_8_5_1_860 14 98 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 98 131 (accept_3_2 13 98 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 98 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 98 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 98 131
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 98 131 (accept_3_2 10 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  98 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 98 131 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 98 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 98 131 (accept_3_2 7 98 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 98 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 98 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 98 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 131 (accept_3_2 4 98 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 98 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 98
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 131
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 98 131 (accept_3_2 1 98 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  131)))))))))))))))))))))))))))))))))) (allB_succ' 35 97 131 (Eq.refl Bool.true) (allA_of_3_0 35 97 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 96 131 (Eq.refl Bool.true) (allA_succ_of_accept 35 96 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 131 (accept_3_2 34 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  96 131 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 96 131 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 96 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 131 (accept_3_2 31 96 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 96 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 131
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 131 (accept_3_2 28 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 131 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 131 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 96 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 131 (accept_3_2 25 96 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 131 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 96 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 131
  (Polychromatic418967fa.accept_17_6_11_12_1_4107 23 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 131 (accept_3_2 22 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 131 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 96 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 131 (accept_3_2 19 96 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 131 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 96 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 131 (accept_3_2 16 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 131 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 131 (Polychromatic418967fa.accept_17_14_11_12_1_4109 14 96 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 131 (accept_3_2 13 96 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 96 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 131
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 131 (accept_3_2 10 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 131 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 131 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 96 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 131 (accept_3_2 7 96 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 131 (Polychromatic418967fa.accept_13_6_5_1_1_834 6 96 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 131
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 131 (accept_3_2 4 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  131 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 96 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 131 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 96 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 131 (accept_3_2 1 96 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96 131)))))))))))))))))))))))))))))))))))) (allB_succ' 37 95 131 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 95 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 95 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 131 (Polychromatic418967fa.accept_21_14_11_5_1_6591 35 95
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 131 (accept_3_2 34 95 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 131
  (Polychromatic418967fa.accept_20_13_15_11_1_6610 33 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 131 (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 95 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 131 (accept_3_2 31 95 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 95 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 131
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 131 (accept_3_2 28 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 131 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 95 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 131 (accept_3_2 25 95 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 131 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 95 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 131
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 131 (accept_3_2 22 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 131 (Polychromatic418967fa.accept_15_6_5_11_1_2378 21 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 95 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 131 (accept_3_2 19 95 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 131 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 95 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 131
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 131 (accept_3_2 16 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 131 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 95 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 131 (accept_3_2 13 95 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 95 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 131
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 131 (accept_3_2 10 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 95 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 131 (accept_3_2 7 95 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 95 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 131
  (Polychromatic418967fa.accept_13_5_4_1_1_364 5 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 131 (accept_3_2 4 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  131 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 95 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 95 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 95 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 131 (accept_3_2 1 95 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 95 131))))))))))))))))))))))))))))))))))))) (allB_succ' 38 94 131 (Eq.refl Bool.true)
  (allA_of_3_0 38 94 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 93 131 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 131 (accept_3_2 37 93 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 131 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 93 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 35
  93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 131 (accept_3_2 34 93
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 131
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 131 (accept_3_2 31 93 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 29
  93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 131 (accept_3_2 28 93
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 131
  (Polychromatic418967fa.accept_12_3_9_11_1_231 27 93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 131 (accept_3_2 25 93 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 93 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 131 (Polychromatic418967fa.accept_15_8_3_11_1_849
  23 93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 131 (accept_3_2 22
  93 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 131
  (Polychromatic418967fa.accept_14_7_9_5_1_529 21 93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 131 (accept_3_2 19 93 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 17
  93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 131 (accept_3_2 16 93
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 131
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 131 (accept_3_2 13 93 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 131 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 93 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 11
  93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 131 (accept_3_2 10 93
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 131
  (Polychromatic418967fa.accept_13_9_2_1_1_813 9 93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 131 (accept_3_2 7 93 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 93 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 131 (Polychromatic418967fa.accept_17_5_8_12_1_6609
  5 93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 131 (accept_3_2 4 93
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 131 (Polychromatic418967fa.accept_7_3_2_5_1_147
  3 93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 93 131 (accept_3_2 1 93 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  131))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 92 131 (Eq.refl Bool.true) (allA_succ_of_accept 39 92 131
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 92 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 92 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 92 131 (accept_3_2 37 92 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 92 131 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 92 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 92 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 35
  92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 131 (accept_3_2 34 92
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 131 (Polychromatic418967fa.accept_6_3_2_5_1_32
  33 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 131
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 131 (accept_3_2 31 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 131 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 92 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 131 (accept_3_2 28 92 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 131 (accept_3_2 25 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 131 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 92 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 131 (accept_3_2 22 92 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 131
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 131 (accept_3_2 19 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 92 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 131 (accept_3_2 16 92 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 131 (accept_3_2 13 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 92 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 131 (accept_3_2 10 92 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 131 (accept_3_2 7 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  131 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 131 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 92 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 131 (accept_3_2 4 92 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 131 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  92 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 131 (accept_3_2 1 92 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92 131)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 91
  131 (Eq.refl Bool.true) (allA_of_3_0 41 91 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 90 131 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 90 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 131 (accept_3_2 40 90 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 90 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 131
  (Polychromatic418967fa.accept_25_13_15_6_1_6608 38 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 90 131 (accept_3_2 37 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  90 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 90 131 (Polychromatic418967fa.accept_19_16_14_17_1_3863 35 90 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 131 (accept_3_2 34 90 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 131
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 131 (accept_3_2 31 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  90 131 (Polychromatic418967fa.accept_19_11_14_17_1_6607 30 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 90 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 131 (accept_3_2 28 90 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 131 (Polychromatic418967fa.accept_14_13_6_5_1_1853 27 90 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 131
  (Polychromatic418967fa.accept_17_9_5_12_1_6606 26 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 90 131 (accept_3_2 25 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  90 131 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 90 131 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 90 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 131 (accept_3_2 22 90 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 131
  (Polychromatic418967fa.accept_19_1_14_17_1_6605 20 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 90 131 (accept_3_2 19 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  90 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 90 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 131 (accept_3_2 16 90 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 90 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 131
  (Polychromatic418967fa.accept_20_14_10_11_1_2393 14 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 90 131 (accept_3_2 13 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 90 131 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 90 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 90 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 131 (accept_3_2 10 90 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 90 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 131
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 90 131 (accept_3_2 7 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90
  131 (Polychromatic418967fa.accept_24_6_18_11_1_6604 6 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 90 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 131 (accept_3_2 4 90 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 131 (Polychromatic418967fa.accept_19_3_14_17_1_6603 3 90 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 131
  (Polychromatic418967fa.accept_13_2_12_1_1_343 2 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 131 (accept_3_2 1 90 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  131)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 89 131 (Eq.refl Bool.true) (allA_succ_of_accept 42 89 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 89 131 (Polychromatic418967fa.accept_17_7_4_12_1_4084 41 89 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 131 (accept_3_2 40 89 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 89 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 89 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 131 (accept_3_2 37 89
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 131
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 89 131 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 89 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 131 (accept_3_2 34 89 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 89 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 89 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 131 (Polychromatic418967fa.accept_10_2_9_1_1_185
  32 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 131 (accept_3_2 31
  89 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 89 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 89 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 131 (accept_3_2 28 89 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 89 131 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 89 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 131 (accept_3_2 25 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 131 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 89 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 131 (accept_3_2 22 89 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 89 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 131
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 131 (accept_3_2 19 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 131 (Polychromatic418967fa.accept_22_17_1_21_1_6602 17 89 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 131 (accept_3_2 16 89 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 89 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 131 (accept_3_2 13 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 89 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 131 (accept_3_2 10 89 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 131 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 89 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 131
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 131 (accept_3_2 7 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 131 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 89 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 131 (accept_3_2 4 89 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 89 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 131 (accept_3_2 1 89 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 131))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 88
  131 (Eq.refl Bool.true) (allA_of_3_0 44 88 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 87 131 (Eq.refl
  Bool.true) (allA_succ_of_accept 44 87 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 131 (accept_3_2 43 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 131 (Polychromatic418967fa.accept_16_10_7_3_1_6601 42 87 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 131
  (Polychromatic418967fa.accept_13_2_9_1_1_67 41 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 131 (accept_3_2 40 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 131 (accept_3_2 37 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 87 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 131 (accept_3_2 34 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 131 (accept_3_2 31 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 87 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 131
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 131 (accept_3_2 28 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 131 (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 131 (accept_3_2 25 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 131 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 87 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 131
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 131 (accept_3_2 22 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 131 (accept_3_2 19 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 131 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 87 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 131 (accept_3_2 16 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 131 (accept_3_2 13 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 87 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 131
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 131 (accept_3_2 10 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 131 (accept_3_2 7 87 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 131 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 87 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 131
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 131 (accept_3_2 4 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  131 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 131 (accept_3_2 1 87 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 131))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 86 131 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 86 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 131 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 86 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 86 131 (accept_3_2 43 86 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 86 131 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  42 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 86 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 86 131 (accept_3_2 40 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  86 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 86 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 86 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 86 131 (accept_3_2 37 86 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 86 131 (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 86 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 86 131
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 86 131 (accept_3_2 34 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  86 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 86 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 86 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 86 131 (accept_3_2 31 86 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 86 131 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 86 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 86 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 86 131 (accept_3_2 28 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  86 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 86 131 (Polychromatic418967fa.accept_18_8_14_5_1_2778 26 86 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 86 131 (accept_3_2 25 86 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 86 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 86 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 86 131
  (Polychromatic418967fa.accept_11_1_9_10_1_184 23 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 86 131 (accept_3_2 22 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  86 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 86 131 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 86 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 86 131 (accept_3_2 19 86 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 86 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 86 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 86 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 86 131 (accept_3_2 16 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  86 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 86 131 (Polychromatic418967fa.accept_20_14_6_11_1_6600 14 86 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 86 131 (accept_3_2 13 86 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 86 131 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 86 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 86 131
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 86 131 (accept_3_2 10 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  86 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 86 131 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 86 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 86 131 (accept_3_2 7 86 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 86 131 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 86 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 86 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 131 (accept_3_2 4 86 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 86 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 131
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 86 131 (accept_3_2 1 86 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  131)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 85 131 (Eq.refl Bool.true) (allA_of_3_0 47 85 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 84 131 (Eq.refl Bool.true) (allA_succ_of_accept 47 84 131
  (Polychromatic418967fa.accept_8_7_4_3_1_156 47 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 131 (accept_3_2 46 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 131 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 131 (accept_3_2 43 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 84 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 131
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 41 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 131 (accept_3_2 40 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 131 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 131 (accept_3_2 37 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 131 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 84 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 131
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 131 (accept_3_2 34 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 131 (Polychromatic418967fa.accept_15_2_9_11_1_1551 32 84 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 131 (accept_3_2 31 84 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 131 (Polychromatic418967fa.accept_17_13_16_12_1_6562 30 84
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 131
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 131 (accept_3_2 28 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 131 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 131 (accept_3_2 25 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 84 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 131
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 131 (accept_3_2 22 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 131 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 131 (accept_3_2 19 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 131 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 84 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 131
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 131 (accept_3_2 16 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 131 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 131 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 131 (accept_3_2 13 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 131 (Polychromatic418967fa.accept_16_12_4_3_1_4295 12 84 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 131
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 131 (accept_3_2 10 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 131 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 131 (accept_3_2 7 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 84 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 131
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 131 (accept_3_2 4 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  131 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 84 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 84 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 131 (accept_3_2 1 84 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84 131)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 83 131 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 83 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 131 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  47 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 83 131 (accept_3_2 46
  83 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 83 131
  (Polychromatic418967fa.accept_13_6_5_1_1_834 45 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 83 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 83 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 131 (accept_3_2 43 83 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 83 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 83 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 131
  (Polychromatic418967fa.accept_22_19_17_21_1_5004 41 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 83 131 (accept_3_2 40 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 83 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 83 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 131 (Polychromatic418967fa.accept_10_8_3_1_1_1316 38 83 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 131 (accept_3_2 37 83 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 36
  83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 131 (accept_3_2 34 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 83 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 131 (accept_3_2 31 83 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 83 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 131
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 131 (accept_3_2 28 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 131 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 83 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 131 (accept_3_2 25 83 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 83 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 131
  (Polychromatic418967fa.accept_21_2_20_5_1_6599 23 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 131 (accept_3_2 22 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 131 (Polychromatic418967fa.accept_14_6_13_5_1_534 20 83 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 131 (accept_3_2 19 83 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 83 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 131 (accept_3_2 16 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 131 (Polychromatic418967fa.accept_17_14_15_12_1_1921 14 83 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 131 (accept_3_2 13 83 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 83 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 131
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 131 (accept_3_2 10 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 131 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 83 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 131 (accept_3_2 7 83 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 131
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 131 (accept_3_2 4 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  131 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 83 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 131 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 83 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 131 (accept_3_2 1 83 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 131))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 82 131 (Eq.refl
  Bool.true) (allA_of_3_0 50 82 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 81 131 (Eq.refl Bool.true)
  (allA_succ_of_accept 50 81 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 131 (accept_3_2 49 81 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 81 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 131 (Polychromatic418967fa.accept_15_2_6_11_1_1587
  47 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 131 (accept_3_2 46
  81 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 131
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 131 (accept_3_2 43 81 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 41
  81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 131 (accept_3_2 40 81
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 131
  (Polychromatic418967fa.accept_12_3_9_11_1_231 39 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 131 (accept_3_2 37 81 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 81 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 131 (Polychromatic418967fa.accept_15_5_6_11_1_854
  35 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 131 (accept_3_2 34
  81 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 131
  (Polychromatic418967fa.accept_13_7_3_1_1_814 33 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 131 (accept_3_2 31 81 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 29
  81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 131 (accept_3_2 28 81
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 131
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 131 (accept_3_2 25 81 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 131 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 81 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 131
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 131 (accept_3_2 22 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 131 (Polychromatic418967fa.accept_19_2_5_17_1_3850 21 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 131 (accept_3_2 19 81 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 131
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 131 (accept_3_2 16 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 131 (accept_3_2 13 81 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 131 (Polychromatic418967fa.accept_18_12_9_5_1_2771 12 81 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 131
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 131 (accept_3_2 10 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 131 (accept_3_2 7 81 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 131
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 131 (accept_3_2 4 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  131 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 81 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 81 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 131 (accept_3_2 1 81 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 81 131))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 80 131
  (Eq.refl Bool.true) (allA_succ_of_accept 51 80 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 131
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 131 (accept_3_2 49 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 80 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 131 (accept_3_2 46 80 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 131
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 131 (accept_3_2 43 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 131 (Polychromatic418967fa.accept_23_18_11_16_1_6598 41 80 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 131 (accept_3_2 40 80 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 131
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 131 (accept_3_2 37 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 131 (Polychromatic418967fa.accept_13_9_2_1_1_813 35 80 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 131 (accept_3_2 34 80 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 131
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 32 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 131 (accept_3_2 31 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 80 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 131 (accept_3_2 28 80 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 131 (accept_3_2 25 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 80 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 131 (accept_3_2 22 80 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 131
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 131 (accept_3_2 19 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 131 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 131 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 80 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 131 (accept_3_2 16 80 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 131 (accept_3_2 13 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 131 (accept_3_2 10 80 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 131
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 131 (accept_3_2 7 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  131 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 80 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 131 (Polychromatic418967fa.accept_23_5_11_16_1_6597 5 80 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 131 (accept_3_2 4 80 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 80
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 131 (accept_3_2 1 80 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80 131))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 79 131 (Eq.refl Bool.true) (allA_of_3_0 53 79 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  54 78 131 (Eq.refl Bool.true) (allA_succ_of_accept 53 78 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 131 (accept_3_2 52 78 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 78 131 (Polychromatic418967fa.accept_15_6_3_11_1_848
  51 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 131
  (Polychromatic418967fa.accept_19_12_2_17_1_5210 50 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 78 131 (accept_3_2 49 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  78 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 78 131 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 131 (accept_3_2 46 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 78 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 78 131 (accept_3_2 43 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  78 131 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 78 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 131 (accept_3_2 40 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 78 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 78 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 131
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 131 (accept_3_2 37 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  78 131 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 78 131 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 131 (accept_3_2 34 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 78 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 131
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 78 131 (accept_3_2 31 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  78 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 78 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 131 (accept_3_2 28 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 78 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 78 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 78 131 (accept_3_2 25 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  78 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 78 131 (Polychromatic418967fa.accept_10_3_8_1_1_182 23 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 131 (accept_3_2 22 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 78 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 131
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 131 (accept_3_2 19 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  78 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 78 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 131 (accept_3_2 16 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 78 131 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 78 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 131
  (Polychromatic418967fa.accept_15_14_3_11_1_850 14 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 78 131 (accept_3_2 13 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  78 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 78 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 131 (accept_3_2 10 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 78 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 78 131 (accept_3_2 7 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78
  131 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 131 (accept_3_2 4 78 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 78 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 78 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 131 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  78 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 131 (accept_3_2 1 78 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 131))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 77 131 (Eq.refl Bool.true) (allA_succ_of_accept 54 77 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 54
  77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 131
  (Polychromatic418967fa.accept_19_15_1_17_1_670 53 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 131 (accept_3_2 52 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 131 (Polychromatic418967fa.accept_14_9_7_5_1_1105 51 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 131 (accept_3_2 49 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 131 (Polychromatic418967fa.accept_17_14_9_12_1_5350 48 77 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 131
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 47 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 131 (accept_3_2 46 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 131 (Polychromatic418967fa.accept_20_5_17_11_1_6571 45 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 131 (Polychromatic418967fa.accept_10_4_7_1_1_471 44 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 131 (accept_3_2 43 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 131
  (Polychromatic418967fa.accept_13_2_12_1_1_343 41 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 131 (accept_3_2 40 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 131 (Polychromatic418967fa.accept_15_9_2_11_1_2391 39 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 131 (accept_3_2 37 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 131 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 77 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 131
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 131 (accept_3_2 34 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 131 (Polychromatic418967fa.accept_16_1_13_3_1_2168 33 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 131 (Polychromatic418967fa.accept_21_11_14_5_1_6596 32 77 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 131 (accept_3_2 31 77 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 131
  (Polychromatic418967fa.accept_19_10_1_17_1_6595 29 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 131 (accept_3_2 28 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 131 (Polychromatic418967fa.accept_34_27_9_29_1_6594 27 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 131 (accept_3_2 25 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 131 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 77 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 131
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 131 (accept_3_2 22 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 131 (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 131 (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 77 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 131 (accept_3_2 19 77 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 131
  (Polychromatic418967fa.accept_16_1_13_3_1_2168 17 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 131 (accept_3_2 16 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 131 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 131 (accept_3_2 13 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 131 (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 77 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 131
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 131 (accept_3_2 10 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 131 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 131 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 131 (accept_3_2 7 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 131
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 131 (accept_3_2 4 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  131 (Polychromatic418967fa.accept_19_3_1_17_1_5159 3 77 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 77 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 131 (accept_3_2 1 77 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 77 131))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 76 131
  (Eq.refl Bool.true) (allA_of_3_0 56 76 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 75 131 (Eq.refl
  Bool.true) (allA_succ_of_accept 56 75 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 131 (accept_3_2 55 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 131 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 75 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 131
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 131 (accept_3_2 52 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  75 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 75 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 131 (accept_3_2 49 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 131 (Polychromatic418967fa.accept_13_9_10_1_1_1389 48 75 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 131
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 131 (accept_3_2 46 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  75 131 (Polychromatic418967fa.accept_11_1_9_10_1_184 45 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 75 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 131 (accept_3_2 43 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 75 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 131
  (Polychromatic418967fa.accept_11_8_9_10_1_503 41 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 75 131 (accept_3_2 40 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  75 131 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 75 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 131 (accept_3_2 37 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 131 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 75 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 131
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 131 (accept_3_2 34 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  75 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 75 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 131 (accept_3_2 31 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 131 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 75 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 131
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 131 (accept_3_2 28 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  75 131 (Polychromatic418967fa.accept_21_6_12_5_1_6593 27 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 75 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 131 (accept_3_2 25 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 75 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 131
  (Polychromatic418967fa.accept_11_1_9_10_1_184 23 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 131 (accept_3_2 22 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  75 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 75 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 131 (accept_3_2 19 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 131 (Polychromatic418967fa.accept_21_18_12_5_1_6592 18 75 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 131
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 131 (accept_3_2 16 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  75 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 75 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 131 (accept_3_2 13 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 131 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 75 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 131
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 131 (accept_3_2 10 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  75 131 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 131 (accept_3_2 7 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 75 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 131
  (Polychromatic418967fa.accept_17_5_7_12_1_1951 5 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 131 (accept_3_2 4 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75
  131 (Polychromatic418967fa.accept_17_3_7_12_1_2016 3 75 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 75 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 131 (accept_3_2 1 75 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 75 131))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 74 131
  (Eq.refl Bool.true) (allA_succ_of_accept 57 74 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 131
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 131 (accept_3_2 55 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 131 (Polychromatic418967fa.accept_13_2_9_1_1_67 54 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 131 (accept_3_2 52 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 74 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 131
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 131 (accept_3_2 49 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 131 (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 131 (accept_3_2 46 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 131
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 131 (accept_3_2 43 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 131 (accept_3_2 40 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 74 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 131
  (Polychromatic418967fa.accept_21_17_11_5_1_5060 38 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 131 (accept_3_2 37 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 131 (accept_3_2 34 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 131
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 131 (accept_3_2 31 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 131 (accept_3_2 28 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 74 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 131 (accept_3_2 25 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 131 (accept_3_2 22 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 131
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 131 (accept_3_2 19 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 131 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 131 (accept_3_2 16 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 74 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 131
  (Polychromatic418967fa.accept_21_14_11_5_1_6591 14 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 131 (accept_3_2 13 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 131 (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 74 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 131 (accept_3_2 10 74 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 131
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 131 (accept_3_2 7 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  131 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 131 (accept_3_2 4 74 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  74 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 131 (accept_3_2 1 74 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74 131))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 73 131 (Eq.refl Bool.true) (allA_of_3_0 59 73 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  60 72 131 (Eq.refl Bool.true) (allA_succ_of_accept 59 72 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 72 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 72 131 (accept_3_2 58 72 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 72 131 (Polychromatic418967fa.accept_21_15_9_5_1_6588
  57 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 131
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 72 131 (accept_3_2 55 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  72 131 (Polychromatic418967fa.accept_21_12_9_5_1_6547 54 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 72 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 131 (accept_3_2 52 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 72 131 (Polychromatic418967fa.accept_19_13_15_17_1_5199 51 72 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 131
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 50 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 131 (accept_3_2 49 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  72 131 (Polychromatic418967fa.accept_19_10_15_17_1_6590 48 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 72 131 (Polychromatic418967fa.accept_13_8_7_1_1_1385 47 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 131 (accept_3_2 46 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 72 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 72 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 131
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 44 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 72 131 (accept_3_2 43 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 72 131 (Polychromatic418967fa.accept_13_3_7_1_1_334 42 72 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 131 (Polychromatic418967fa.accept_17_7_4_12_1_4084 41 72
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 131 (accept_3_2 40 72 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 72 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 39
  72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 131
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 72 131 (accept_3_2 37 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  72 131 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 72 131 (Polychromatic418967fa.accept_14_7_2_5_1_4528 35 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 131 (accept_3_2 34 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 72 131 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 72 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 131
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 131 (accept_3_2 31 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  72 131 (Polychromatic418967fa.accept_23_7_3_16_1_6589 30 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 72 131 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 131 (accept_3_2 28 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 72 131 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 72 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 131
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 72 131 (accept_3_2 25 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  72 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 72 131 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 131 (accept_3_2 22 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 72 131 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 72 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 131
  (Polychromatic418967fa.accept_16_4_8_3_1_4206 20 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 72 131 (accept_3_2 19 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  72 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 72 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 131 (accept_3_2 16 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 72 131 (Polychromatic418967fa.accept_21_15_9_5_1_6588 15 72 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 131
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 72 131 (accept_3_2 13 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 72 131 (Polychromatic418967fa.accept_16_12_8_3_1_4241 12 72 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 72 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 131 (accept_3_2 10 72 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 72 131 (Polychromatic418967fa.accept_10_9_2_1_1_840 9
  72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 131
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 72 131 (accept_3_2 7 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72
  131 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 131 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 72 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 131 (accept_3_2 4 72 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 72 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 131 (Polychromatic418967fa.accept_17_2_4_12_1_6587
  2 72 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 131 (accept_3_2 1 72
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  131)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 71 131 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 71 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 71 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 71 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 131 (accept_3_2 58 71 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 57
  71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 131
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 71 131 (accept_3_2 55 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 131 (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 131 (accept_3_2 52 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 71 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 131
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 50 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 131 (accept_3_2 49 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 131 (accept_3_2 46 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 71 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 131
  (Polychromatic418967fa.accept_8_4_7_3_1_144 44 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 131 (accept_3_2 43 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 131 (accept_3_2 40 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 71 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 131
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 131 (accept_3_2 37 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 131 (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 131 (accept_3_2 34 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 71 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 131
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 131 (accept_3_2 31 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 131 (accept_3_2 28 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 71 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 131
  (Polychromatic418967fa.accept_11_4_5_10_1_926 26 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 131 (accept_3_2 25 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 131 (Polychromatic418967fa.accept_21_2_8_5_1_5057 23 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 131 (accept_3_2 22 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 71 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 131
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 131 (accept_3_2 19 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 131 (accept_3_2 16 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 71 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 131
  (Polychromatic418967fa.accept_21_14_8_5_1_6586 14 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 131 (accept_3_2 13 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 131 (accept_3_2 10 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 131 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 71 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 131
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 131 (accept_3_2 7 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  131 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 131 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 71 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 131 (accept_3_2 4 71 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 71 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  71 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 131 (accept_3_2 1 71 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 131)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 70 131 (Eq.refl Bool.true) (allA_of_3_0 62 70 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  63 69 131 (Eq.refl Bool.true) (allA_succ_of_accept 62 69 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 131 (accept_3_2 61 69 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 69 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 60
  69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 131
  (Polychromatic418967fa.accept_19_2_12_17_1_5197 59 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 69 131 (accept_3_2 58 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  69 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 69 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 131 (accept_3_2 55 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 131
  (Polychromatic418967fa.accept_7_4_6_5_1_141 53 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 69 131 (accept_3_2 52 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  69 131 (Polychromatic418967fa.accept_11_7_3_10_1_1461 51 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 69 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 131 (accept_3_2 49 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 131
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 131 (accept_3_2 46 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  69 131 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 69 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 131 (accept_3_2 43 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 131
  (Polychromatic418967fa.accept_19_3_12_17_1_6585 41 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 131 (accept_3_2 40 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  69 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 69 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 131 (accept_3_2 37 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 69 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 131 (accept_3_2 34 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  69 131 (Polychromatic418967fa.accept_17_16_1_12_1_6584 33 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 69 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 131 (accept_3_2 31 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 131
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 131 (accept_3_2 28 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 131 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 131 (accept_3_2 25 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 131 (Polychromatic418967fa.accept_16_8_5_3_1_4297 24 69 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 131
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 131 (accept_3_2 22 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  69 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 69 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 131 (accept_3_2 19 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 131 (accept_3_2 16 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 131 (accept_3_2 13 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 69 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 131
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 131 (accept_3_2 10 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 131 (Polychromatic418967fa.accept_18_9_15_5_1_6551 9 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 131 (accept_3_2 7 69 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 131
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 131 (accept_3_2 4 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  131 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 69 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 131 (accept_3_2 1 69 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 131))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 68 131
  (Eq.refl Bool.true) (allA_succ_of_accept 63 68 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 131 (accept_3_2 61 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 131 (Polychromatic418967fa.accept_16_12_4_3_1_4295 60 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 131 (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 131 (accept_3_2 58 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 131
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 131 (accept_3_2 55 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 131 (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 131 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 131 (accept_3_2 52 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 131 (accept_3_2 49 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 131 (Polychromatic418967fa.accept_15_3_8_11_1_4386 48 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 131 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 131 (accept_3_2 46 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 131
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 44 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 131 (accept_3_2 43 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 131 (Polychromatic418967fa.accept_15_12_8_11_1_4383 42 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 131 (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 131 (accept_3_2 40 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 131 (accept_3_2 37 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 131 (Polychromatic418967fa.accept_22_14_2_21_1_6583 36 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 131 (Polychromatic418967fa.accept_14_7_12_5_1_1861 35 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 131 (accept_3_2 34 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 131
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 32 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 131 (accept_3_2 31 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 131 (Polychromatic418967fa.accept_13_4_3_1_1_2898 30 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 131 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 131 (accept_3_2 28 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 131 (accept_3_2 25 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 131 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 131 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 131 (accept_3_2 22 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 131
  (Polychromatic418967fa.accept_13_7_3_1_1_814 20 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 131 (accept_3_2 19 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 131 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 131 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 131 (accept_3_2 16 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 131 (accept_3_2 13 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 131 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 131 (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 131 (accept_3_2 10 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 131
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 8 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 131 (accept_3_2 7 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  131 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 68 131 (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 131 (accept_3_2 4 68 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 68 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 68 131 (accept_3_2 1 68 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  131)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 67 131 (Eq.refl Bool.true)
  (allA_of_3_0 65 67 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 131 (allA_succ_of_accept 65 66 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 131 (accept_3_2 64 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 131 (Polychromatic418967fa.accept_15_3_6_11_1_855 63 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 131 (accept_3_2 61 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 66 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 131
  (Polychromatic418967fa.accept_19_2_9_17_1_626 59 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 131 (accept_3_2 58 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 131 (accept_3_2 55 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 131 (Polychromatic418967fa.accept_14_12_10_5_1_2712 54 66 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 131 (accept_3_2 52 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 131 (accept_3_2 49 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 131 (Polychromatic418967fa.accept_15_3_6_11_1_855 48 66 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 131
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 131 (accept_3_2 46 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 131 (accept_3_2 43 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 66 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 131 (accept_3_2 40 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 131 (Polychromatic418967fa.accept_15_9_6_11_1_1586 39 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 131 (accept_3_2 37 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 66 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 131
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 131 (accept_3_2 34 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 131 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 131 (accept_3_2 31 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 66 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 131 (accept_3_2 28 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 131 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 131 (accept_3_2 25 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 66 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 131
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 131 (accept_3_2 22 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 131 (accept_3_2 19 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 131 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 66 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 131 (accept_3_2 16 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 131 (Polychromatic418967fa.accept_17_14_15_12_1_1921 14 66 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 131 (accept_3_2 13 66 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 131 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 66 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 131
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 131 (accept_3_2 10 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 66 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 131 (accept_3_2 7 66 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 66 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 66 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 131 (accept_3_2 4 66 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 131 (Polychromatic418967fa.accept_15_3_6_11_1_855 3
  66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 131
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 131 (accept_3_2 1 66 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  131)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 131 (allA_succ_of_accept 64 65 131
  (accept_3_2 64 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 131
  (Polychromatic418967fa.accept_14_7_9_5_1_529 63 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 131 (accept_3_2 61 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 65 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 59
  65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 131 (accept_3_2 58 65
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 131
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 65 131 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 131 (accept_3_2 55 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 65 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 53
  65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 131 (accept_3_2 52 65
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 131
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 65 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 131 (accept_3_2 49 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 65 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 65 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 131 (Polychromatic418967fa.accept_15_2_5_11_1_1563
  47 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 131 (accept_3_2 46
  65 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 131
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 65 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 131 (accept_3_2 43 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 65 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 131 (Polychromatic418967fa.accept_19_3_8_17_1_5213
  41 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 131 (accept_3_2 40
  65 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 131
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 65 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 131 (accept_3_2 37 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 65 131 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 65 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 35
  65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 131 (accept_3_2 34 65
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 131
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 131 (accept_3_2 31 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 65 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 131 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  29 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 131 (accept_3_2 28
  65 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 131
  (Polychromatic418967fa.accept_24_3_17_11_1_6582 27 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 65 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 131 (accept_3_2 25 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 65 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 65 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 131 (Polychromatic418967fa.accept_15_8_5_11_1_2358
  23 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 131 (accept_3_2 22
  65 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 131
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 65 131 (Polychromatic418967fa.accept_16_4_1_3_1_6581 20 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 131 (accept_3_2 19 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 65 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 17
  65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 131 (accept_3_2 16 65
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 131
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 65 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 131 (accept_3_2 13 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 65 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 65 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 11
  65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 131 (accept_3_2 10 65
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 131
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 65 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 131 (accept_3_2 7 65 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 65 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 131 (Polychromatic418967fa.accept_24_5_17_11_1_6580
  5 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 131 (accept_3_2 4 65
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 131 (Polychromatic418967fa.accept_7_3_2_5_1_147
  3 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 131 (accept_3_2 1 65 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  131))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 131 (allA_of_3_0 64 64 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 131 (allA_succ_of_accept 62 63 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 131 (accept_3_2 61 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 131 (Polychromatic418967fa.accept_13_7_11_1_1_2903 59 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 131 (accept_3_2 58 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 63
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 131 (accept_3_2 55 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 131 (Polychromatic418967fa.accept_14_12_7_5_1_1107 54 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 131 (Polychromatic418967fa.accept_11_9_8_10_1_934 53 63 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 131 (accept_3_2 52 63 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 131 (Polychromatic418967fa.accept_13_12_11_1_1_2920 51 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 131 (accept_3_2 49 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 131 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 131 (Polychromatic418967fa.accept_13_8_11_1_1_3789 47 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 131 (accept_3_2 46 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 63
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 131 (accept_3_2 43 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 131 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 131 (Polychromatic418967fa.accept_19_3_6_17_1_6579 41 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 131 (accept_3_2 40 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 131 (Polychromatic418967fa.accept_16_7_15_3_1_1302 39 63
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 131 (accept_3_2 37 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 131 (Polychromatic418967fa.accept_13_9_11_1_1_1375 35 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 131 (accept_3_2 34 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 63
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 131 (accept_3_2 31 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 131 (Polychromatic418967fa.accept_14_2_7_5_1_5450 30 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 131 (Polychromatic418967fa.accept_13_3_11_1_1_2122 29 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 131 (accept_3_2 28 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 131 (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 63
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 131 (accept_3_2 25 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 131 (Polychromatic418967fa.accept_22_2_19_21_1_6578 24 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 131 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 131 (accept_3_2 22 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 63
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 131 (accept_3_2 19 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 131 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 131 (Polychromatic418967fa.accept_22_17_19_21_1_6577 17 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 131 (accept_3_2 16 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 131 (Polychromatic418967fa.accept_18_15_9_5_1_3934 15 63
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 131 (accept_3_2 13 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 131 (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 131 (accept_3_2 10 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 131 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 63 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 131 (accept_3_2 7 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  131 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 131 (Polychromatic418967fa.accept_27_5_9_23_1_6576 5 63 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 131 (accept_3_2 4 63 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 131 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 63 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 131 (accept_3_2 1 63 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  131))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 131 (allA_succ_of_accept 61 62 131
  (accept_3_2 61 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 131
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 131 (Polychromatic418967fa.accept_10_9_2_1_1_840 59 62 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 131 (accept_3_2 58 62 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 56
  62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 131 (accept_3_2 55 62
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 131
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 131 (accept_3_2 52 62 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 50
  62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 131 (accept_3_2 49 62
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 131 (Polychromatic418967fa.accept_9_3_8_5_1_65
  48 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 62 131
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 62 131 (accept_3_2 46 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  62 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 62 131 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 131 (accept_3_2 43 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 62 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 62 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 62 131 (accept_3_2 40 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  62 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 62 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 131 (accept_3_2 37 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 62 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 131
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 131 (accept_3_2 34 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  62 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 62 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 131 (accept_3_2 31 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 62 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 131 (accept_3_2 28 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 131 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 131 (accept_3_2 25 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 62 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 131
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 131 (accept_3_2 22 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 131 (accept_3_2 19 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 62 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 131 (accept_3_2 16 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 131 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 131 (accept_3_2 13 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 62 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 131
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 131 (accept_3_2 10 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 62 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 62 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 131 (accept_3_2 7 62 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 62 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 62 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 131 (accept_3_2 4 62 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 131
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 62 131 (accept_3_2 1 62 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  131)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 131 (allA_of_3_0 61 61 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 131 (allA_succ_of_accept 59 60 131
  (Polychromatic418967fa.accept_11_4_5_10_1_926 59 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 131 (accept_3_2 58 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 131 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 131 (accept_3_2 55 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 131 (Polychromatic418967fa.accept_19_16_3_17_1_6575 54 60 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 131 (accept_3_2 52 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 131 (accept_3_2 49 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 60 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 131
  (Polychromatic418967fa.accept_8_7_4_3_1_156 47 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 131 (accept_3_2 46 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 131 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 131 (accept_3_2 43 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 131 (Polychromatic418967fa.accept_16_10_12_3_1_4252 42 60 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 131
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 131 (accept_3_2 40 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 131 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 131 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 131 (accept_3_2 37 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 60 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 131 (accept_3_2 34 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 131 (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 131 (Polychromatic418967fa.accept_13_6_8_1_1_2913 32 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 131 (accept_3_2 31 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 60 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 131
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 131 (accept_3_2 28 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 131 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 131 (accept_3_2 25 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 131 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 60 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 131
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 131 (accept_3_2 22 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 131 (accept_3_2 19 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 131 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 60 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 131 (accept_3_2 16 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 131 (Polychromatic418967fa.accept_17_14_9_12_1_5350 14 60 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 131 (accept_3_2 13 60 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 60 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 131
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 131 (accept_3_2 10 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 131 (accept_3_2 7 60 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 60 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 131
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 131 (accept_3_2 4 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  131 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 60 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 131 (accept_3_2 1 60 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 131)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 131
  (allA_succ_of_accept 58 59 131 (accept_3_2 58 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 131 (Polychromatic418967fa.accept_16_8_11_3_1_4279 56 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 131 (accept_3_2 55 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 131 (Polychromatic418967fa.accept_14_12_3_5_1_1868 54 59
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 131
  (Polychromatic418967fa.accept_19_15_2_17_1_5163 53 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 131 (accept_3_2 52 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 59 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 131 (accept_3_2 49 59 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 131 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 131
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 47 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 131 (accept_3_2 46 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 131 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 59 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 131 (accept_3_2 43 59 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 131 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 131
  (Polychromatic418967fa.accept_19_3_2_17_1_6574 41 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 131 (accept_3_2 40 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 131 (Polychromatic418967fa.accept_16_7_11_3_1_1330 39 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 131 (Polychromatic418967fa.accept_10_8_9_1_1_189 38 59 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 131 (accept_3_2 37 59 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 131
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 131 (accept_3_2 34 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 131 (Polychromatic418967fa.accept_15_3_14_11_1_1579 33 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 131 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 59 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 131 (accept_3_2 31 59 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 131
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 131 (accept_3_2 28 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 131 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 131 (Polychromatic418967fa.accept_14_12_3_5_1_1868 26 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 131 (accept_3_2 25 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 131 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 59
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 131
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 131 (accept_3_2 22 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 131 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 131 (Polychromatic418967fa.accept_17_3_8_12_1_6573 20 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 131 (accept_3_2 19 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 131 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 59 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 131
  (Polychromatic418967fa.accept_25_17_9_6_1_6572 17 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 131 (accept_3_2 16 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 131 (Polychromatic418967fa.accept_16_14_11_3_1_4249 14 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 131 (accept_3_2 13 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 131 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 59 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 131
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 131 (accept_3_2 10 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 59 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 131 (accept_3_2 7 59 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 131 (Polychromatic418967fa.accept_13_6_7_1_1_335 6 59 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 131
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 131 (accept_3_2 4 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  131 (Polychromatic418967fa.accept_13_3_7_1_1_334 3 59 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 59 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 131 (accept_3_2 1 59 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 131))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 131 (allA_of_3_0
  58 58 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 131 (allA_succ_of_accept 56 57 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 131 (accept_3_2 55 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 131 (accept_3_2 52 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 57 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 131 (accept_3_2 49 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 131 (accept_3_2 46 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 57 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 131 (accept_3_2 43 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 131 (accept_3_2 40 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 57 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 131 (accept_3_2 37 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 131 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 131 (accept_3_2 34 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 57 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 131 (accept_3_2 31 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 131 (accept_3_2 28 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 57 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 131 (accept_3_2 25 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 131 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 57 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 131 (accept_3_2 22 57 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 131 (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 57 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 131 (accept_3_2 19 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 131 (accept_3_2 16 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 131 (accept_3_2 13 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 131 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 131 (accept_3_2 10 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 131 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 57 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 131 (accept_3_2 7 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 131 (Polychromatic418967fa.accept_20_5_17_11_1_6571 5 57 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 131 (accept_3_2 4 57 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 57 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 131 (accept_3_2 1 57 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 131)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 131 (allA_succ_of_accept 55 56 131 (accept_3_2 55 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 131 (Polychromatic418967fa.accept_19_16_18_17_1_6570 54 56 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 131 (accept_3_2 52 56 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 131 (accept_3_2 49 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 131 (Polychromatic418967fa.accept_10_7_6_1_1_486 47 56 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 131 (accept_3_2 46 56 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 131 (accept_3_2 43 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 131 (Polychromatic418967fa.accept_17_7_5_12_1_1997 41 56 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 131 (accept_3_2 40 56 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 131 (accept_3_2 37 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 131 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 131 (accept_3_2 34 56 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 131
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 131 (accept_3_2 31 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 131 (Polychromatic418967fa.accept_13_3_4_1_1_363 29 56 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 131 (accept_3_2 28 56 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 131 (accept_3_2 25 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 131 (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 56 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 131 (accept_3_2 22 56 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 131
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 131 (accept_3_2 19 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 131 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 131 (accept_3_2 16 56 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 131 (accept_3_2 13 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 131 (Polychromatic418967fa.accept_16_11_8_3_1_3183 11 56 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 131 (accept_3_2 10 56 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 131 (accept_3_2 7 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  131 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 131 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 56 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 131 (accept_3_2 4 56 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 131 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  56 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 131 (accept_3_2 1 56 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 131))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 131 (allA_of_3_0 55 55 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 131
  (allA_succ_of_accept 53 54 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 131 (accept_3_2 52 54 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 131 (Polychromatic418967fa.accept_13_12_2_1_1_2909 51 54 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 131
  (Polychromatic418967fa.accept_15_5_9_11_1_4398 50 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 54 131 (accept_3_2 49 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  54 131 (Polychromatic418967fa.accept_13_9_2_1_1_813 48 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 54 131 (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 54 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 131 (accept_3_2 46 54 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 54 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 131
  (Polychromatic418967fa.accept_23_21_8_16_1_6569 44 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 131 (accept_3_2 43 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  54 131 (Polychromatic418967fa.accept_13_3_2_1_1_2907 42 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 54 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 131 (accept_3_2 40 54 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 54 131 (Polychromatic418967fa.accept_19_1_16_17_1_3864 39 54 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 131
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 38 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 131 (accept_3_2 37 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  54 131 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 54 131 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 54 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 131 (accept_3_2 34 54 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 54 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 131
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 32 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 54 131 (accept_3_2 31 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  54 131 (Polychromatic418967fa.accept_20_10_14_11_1_6568 30 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 54 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 131 (accept_3_2 28 54 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 131 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 54 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 131
  (Polychromatic418967fa.accept_19_7_16_17_1_6567 26 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 131 (accept_3_2 25 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  54 131 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 131 (Polychromatic418967fa.accept_20_3_14_11_1_6566 23 54 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 131 (accept_3_2 22 54 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 131
  (Polychromatic418967fa.accept_15_5_9_11_1_4398 20 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 131 (accept_3_2 19 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 131 (Polychromatic418967fa.accept_16_2_6_3_1_5396 18 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 131 (accept_3_2 16 54 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 131 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 54 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 131
  (Polychromatic418967fa.accept_19_14_16_17_1_6565 14 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 54 131 (accept_3_2 13 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 54 131 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 54 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 131 (Polychromatic418967fa.accept_16_11_6_3_1_6564 11 54
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 131 (accept_3_2 10 54 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 131
  (Polychromatic418967fa.accept_17_8_3_12_1_5354 8 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 131 (accept_3_2 7 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  131 (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 54 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 131 (accept_3_2 4 54 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 131 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 54 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 131
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 131 (accept_3_2 1 54 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  131)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 131 (allA_succ_of_accept 52 53 131 (accept_3_2
  52 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 131
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 131 (accept_3_2 49 53 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 53 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 47
  53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 131 (accept_3_2 46 53
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 131
  (Polychromatic418967fa.accept_11_1_9_10_1_184 45 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 53 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 131 (accept_3_2 43 53 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 41
  53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 131 (accept_3_2 40 53
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 131 (Polychromatic418967fa.accept_9_3_8_5_1_65
  39 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 131 (accept_3_2 37 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 131 (Polychromatic418967fa.accept_15_5_8_11_1_2350 35 53 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 131 (accept_3_2 34 53 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 53 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 131
  (Polychromatic418967fa.accept_10_2_3_1_1_481 32 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 131 (accept_3_2 31 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 53 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 131 (accept_3_2 28 53 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 53 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 131 (accept_3_2 25 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 53 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 131 (accept_3_2 22 53 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 53 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 131
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 131 (accept_3_2 19 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 131 (Polychromatic418967fa.accept_21_17_11_5_1_5060 17 53 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 131 (accept_3_2 16 53 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 53 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 131 (accept_3_2 13 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 131 (accept_3_2 10 53 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 53 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 131
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 131 (accept_3_2 7 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 131 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 53 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 131 (accept_3_2 4 53 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 53 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 131 (accept_3_2 1 53 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 131)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 131 (allA_of_3_0 52 52 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 131
  (allA_succ_of_accept 50 51 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 51 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 131 (accept_3_2 49 51 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 131 (Polychromatic418967fa.accept_9_2_6_5_1_227 47
  51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 131 (accept_3_2 46 51
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 131
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 131 (accept_3_2 43 51 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 131 (Polychromatic418967fa.accept_18_6_15_5_1_6563 42 51 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 131
  (Polychromatic418967fa.accept_13_2_12_1_1_343 41 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 131 (accept_3_2 40 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  51 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 51 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 131 (accept_3_2 37 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 131 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 51 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 131 (accept_3_2 34 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  51 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 51 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 131 (accept_3_2 31 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 131
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 131 (accept_3_2 28 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  51 131 (Polychromatic418967fa.accept_18_9_15_5_1_6551 27 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 51 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 131 (accept_3_2 25 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 131
  (Polychromatic418967fa.accept_19_4_13_17_1_5137 23 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 131 (accept_3_2 22 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  51 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 51 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 131 (accept_3_2 19 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 51 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 131
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 131 (accept_3_2 16 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  51 131 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 51 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 131 (accept_3_2 13 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 51 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 131
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 131 (accept_3_2 10 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  51 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 51 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 131 (accept_3_2 7 51 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 131 (Polychromatic418967fa.accept_18_6_15_5_1_6563 6 51 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 131
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 131 (accept_3_2 4 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51
  131 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 51 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 131 (accept_3_2 1 51 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 51 131))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 131 (allA_succ_of_accept
  49 50 131 (accept_3_2 49 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 131
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 131 (Polychromatic418967fa.accept_13_8_11_1_1_3789 47 50 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 131 (accept_3_2 46 50 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 50 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 131 (Polychromatic418967fa.accept_12_8_2_11_1_246
  44 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 131 (accept_3_2 43
  50 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 131
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 42 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 131 (accept_3_2 40 50 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 38
  50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 131 (accept_3_2 37 50
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 131
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 131 (Polychromatic418967fa.accept_13_9_11_1_1_1375 35 50 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 131 (accept_3_2 34 50 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 32
  50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 131 (accept_3_2 31 50
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 50 131
  (Polychromatic418967fa.accept_17_13_16_12_1_6562 30 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 131 (accept_3_2 28 50 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 50 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 131
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 26 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 131 (accept_3_2 25 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 131 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 50 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 131 (accept_3_2 22 50 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 131
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 131 (accept_3_2 19 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 131 (accept_3_2 16 50 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 50 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 131
  (Polychromatic418967fa.accept_19_14_12_17_1_5196 14 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 50 131 (accept_3_2 13 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 50 131 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 50 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 50 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 131 (accept_3_2 10 50 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 131
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 131 (accept_3_2 7 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  131 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 131 (accept_3_2 4 50 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 50 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 131 (Polychromatic418967fa.accept_15_2_5_11_1_1563
  2 50 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 131 (accept_3_2 1 50
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 131))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 131 (allA_of_3_0 49 49 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 131
  (allA_succ_of_accept 47 48 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 48 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 131 (accept_3_2 46 48 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 48 131 (Polychromatic418967fa.accept_13_6_9_1_1_5604 45 48 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 44
  48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 131 (accept_3_2 43 48
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 131
  (Polychromatic418967fa.accept_9_6_3_5_1_240 42 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 131 (Polychromatic418967fa.accept_13_2_9_1_1_67 41 48 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 131 (accept_3_2 40 48 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 38
  48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 131 (accept_3_2 37 48
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 131 (Polychromatic418967fa.accept_7_1_6_5_1_39
  36 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 131
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 131 (accept_3_2 34 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 48 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 131 (accept_3_2 31 48 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 131 (Polychromatic418967fa.accept_22_8_4_21_1_6561 30 48 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 131
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 131 (accept_3_2 28 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 131 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 48 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 131 (accept_3_2 25 48 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 48 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 131
  (Polychromatic418967fa.accept_10_3_8_1_1_182 23 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 131 (accept_3_2 22 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 131 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 48 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 131 (accept_3_2 19 48 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 48 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 131
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 131 (accept_3_2 16 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 131 (Polychromatic418967fa.accept_15_14_3_11_1_850 14 48 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 131 (accept_3_2 13 48 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 131 (Polychromatic418967fa.accept_19_12_10_17_1_5189 12 48
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 131
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 131 (accept_3_2 10 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 131 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 48 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 131 (accept_3_2 7 48 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 48 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 131
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 131 (accept_3_2 4 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  131 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 48 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 48 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 131 (accept_3_2 1 48 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 131)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 131 (allA_succ_of_accept 46
  47 131 (accept_3_2 46 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 131
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 47 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 131 (accept_3_2 43 47 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 47 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 131 (Polychromatic418967fa.accept_20_1_7_11_1_3673
  41 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 131 (accept_3_2 40
  47 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 131
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 131 (Polychromatic418967fa.accept_13_12_8_1_1_825 38 47 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 131 (accept_3_2 37 47 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 47 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 35
  47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 131 (accept_3_2 34 47
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 131
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 131 (Polychromatic418967fa.accept_13_6_8_1_1_2913 32 47 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 131 (accept_3_2 31 47 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 47 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 131 (Polychromatic418967fa.accept_11_7_3_10_1_1461
  29 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 131 (accept_3_2 28
  47 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 131
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 131 (accept_3_2 25 47 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 131 (Polychromatic418967fa.accept_16_7_15_3_1_1302
  23 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 131 (accept_3_2 22
  47 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 131
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 47 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 131 (accept_3_2 19 47 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 131 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 47 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 131 (accept_3_2 16 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 131 (Polychromatic418967fa.accept_10_4_7_1_1_471 14 47 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 131 (accept_3_2 13 47 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 47 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 131
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 131 (accept_3_2 10 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 131 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 47 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 131 (accept_3_2 7 47 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 47 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 131
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 131 (accept_3_2 4 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  131 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 47 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 131 (Polychromatic418967fa.accept_16_2_15_3_1_1300 2 47 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 131 (accept_3_2 1 47 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 131))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 131 (allA_of_3_0 46 46 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 131 (allA_succ_of_accept 44 45 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 131 (accept_3_2 43 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 131 (Polychromatic418967fa.accept_13_2_6_1_1_3807 41 45 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 131 (accept_3_2 40 45 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 131 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 45 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 131 (accept_3_2 37 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 131 (Polychromatic418967fa.accept_11_2_1_10_1_196 35 45 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 131 (accept_3_2 34 45 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 131 (Polychromatic418967fa.accept_13_7_6_1_1_368 33 45 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 131 (accept_3_2 31 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 45 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 131 (accept_3_2 28 45 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 131 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 45 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 131 (accept_3_2 25 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 131 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 45 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 131 (accept_3_2 22 45 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 131 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 45 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 131 (accept_3_2 19 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 131 (Polychromatic418967fa.accept_16_1_13_3_1_2168 17 45 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 131 (accept_3_2 16 45 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 45 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 131 (accept_3_2 13 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 131 (Polychromatic418967fa.accept_14_12_3_5_1_1868 12 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 131 (Polychromatic418967fa.accept_22_11_1_21_1_6560 11 45 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 131 (accept_3_2 10 45 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 131 (accept_3_2 7 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 131 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 45 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 131 (accept_3_2 4 45 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 131 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 45 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 131 (accept_3_2 1 45 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 131))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  131 (allA_succ_of_accept 43 44 131 (accept_3_2 43 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 131 (Polychromatic418967fa.accept_16_9_12_3_1_3138 41 44 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 131 (accept_3_2 40 44 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 131
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 131 (accept_3_2 37 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 131 (Polychromatic418967fa.accept_16_4_12_3_1_2180 36 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 131 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 44 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 131 (accept_3_2 34 44 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 131
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 131 (accept_3_2 31 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 44 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 131 (accept_3_2 28 44 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 131 (accept_3_2 25 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 131 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 44 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 131 (accept_3_2 22 44 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 131
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 131 (accept_3_2 19 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 44 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 131 (accept_3_2 16 44 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 131
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 131 (accept_3_2 13 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 44 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 131 (accept_3_2 10 44 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 131
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 131 (accept_3_2 7 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  131 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 131 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 44 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 131 (accept_3_2 4 44 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  44 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 131 (accept_3_2 1 44 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 131)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  131 (allA_of_3_0 43 43 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 131 (allA_succ_of_accept 41 42 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 131 (accept_3_2 40 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 131 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 42 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 131 (accept_3_2 37 42 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 131 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 131 (accept_3_2 34 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 131 (Polychromatic418967fa.accept_13_6_3_1_1_1413 32 42 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 131 (accept_3_2 31 42 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 42 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 131 (accept_3_2 28 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 131 (Polychromatic418967fa.accept_17_10_8_12_1_6559 27 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 131 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 42 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 131 (accept_3_2 25 42 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 131 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 42 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 131
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 131 (accept_3_2 22 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 131 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 42 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 131 (accept_3_2 19 42 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 131 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 42 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 131 (accept_3_2 16 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 131 (Polychromatic418967fa.accept_13_2_3_1_1_3823 15 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 131 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 42 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 131 (accept_3_2 13 42 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 42 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 131
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 131 (accept_3_2 10 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 131 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 42 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 131 (accept_3_2 7 42 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 42 131 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 42 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 131 (accept_3_2 4 42 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 131
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 131 (accept_3_2 1 42 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  131)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 131 (allA_succ_of_accept 40 41 131 (accept_3_2 40 41 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 39
  41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 131 (accept_3_2 37 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 131 (Polychromatic418967fa.accept_13_9_2_1_1_813 35 41 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 131 (accept_3_2 34 41 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 131 (Polychromatic418967fa.accept_19_14_3_17_1_6558 33 41 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 131
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 131 (accept_3_2 31 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 41 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 131 (accept_3_2 28 41 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 131 (Polychromatic418967fa.accept_19_8_3_17_1_5181 27 41 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 131 (accept_3_2 25 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 131 (Polychromatic418967fa.accept_19_5_3_17_1_6557 24 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 131 (Polychromatic418967fa.accept_16_7_9_3_1_1324 23 41 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 131 (accept_3_2 22 41 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 131 (Polychromatic418967fa.accept_17_4_7_12_1_6556 21 41 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 131
  (Polychromatic418967fa.accept_11_9_8_10_1_934 20 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 131 (accept_3_2 19 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 131 (Polychromatic418967fa.accept_20_17_1_11_1_6555 17 41 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 131 (accept_3_2 16 41 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 41 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 131 (accept_3_2 13 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 131 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 41 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 131 (accept_3_2 10 41 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 131 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 41 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 131
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 131 (accept_3_2 7 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 131 (Polychromatic418967fa.accept_17_5_7_12_1_1951 5 41 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 131 (accept_3_2 4 41 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 131 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 41 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 131 (accept_3_2 1 41 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 131))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 131
  (allA_of_3_0 40 40 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 131 (allA_succ_of_accept 38 39 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 131 (accept_3_2 37 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 39 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 131 (accept_3_2 34 39 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 39 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 131 (accept_3_2 31 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 39 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 131 (accept_3_2 28 39 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 131 (accept_3_2 25 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 39 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 131 (accept_3_2 22 39 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 39 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 131 (accept_3_2 19 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 131 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 39 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 131 (accept_3_2 16 39 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 131 (accept_3_2 13 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 39 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 131 (accept_3_2 10 39 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 39 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 131 (accept_3_2 7 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  131 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 39 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 131 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 39 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 131 (accept_3_2 4 39 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 131 (Polychromatic418967fa.accept_19_3_1_17_1_5159 3 39 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 131 (accept_3_2 1 39 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 131))))))))))))))))))))))))))))))))))))))) (allB_succ 38 131
  (allA_succ_of_accept 37 38 131 (accept_3_2 37 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 131 (accept_3_2 34 38 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 131
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 131 (accept_3_2 31 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 131 (accept_3_2 28 38 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 131 (accept_3_2 25 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 38 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 131 (accept_3_2 22 38 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 131
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 131 (accept_3_2 19 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 131 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 131 (accept_3_2 16 38 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 38 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 131
  (Polychromatic418967fa.accept_21_14_17_5_1_3459 14 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 131 (accept_3_2 13 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 131 (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 38 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 131 (accept_3_2 10 38 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 131
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 131 (accept_3_2 7 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  131 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 38 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 131 (accept_3_2 4 38 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 38
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 131 (accept_3_2 1 38 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 131)))))))))))))))))))))))))))))))))))))) (allB_succ 37 131
  (allA_of_3_0 37 37 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 131 (allA_succ_of_accept 35 36 131
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 131 (accept_3_2 34 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 131 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 36 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 131 (accept_3_2 31 36 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 131 (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 36 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 131
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 131 (accept_3_2 28 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 131 (Polychromatic418967fa.accept_20_6_16_11_1_2379 26 36 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 131 (accept_3_2 25 36 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 36 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 131
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 131 (accept_3_2 22 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 131 (Polychromatic418967fa.accept_17_4_2_12_1_6554 21 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 36 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 131 (accept_3_2 19 36 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 36 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 131
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 131 (accept_3_2 16 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 131 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 131 (Polychromatic418967fa.accept_21_14_15_5_1_6553 14 36 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 131 (accept_3_2 13 36 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 131 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 36 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 131
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 131 (accept_3_2 10 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 131 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 131 (Polychromatic418967fa.accept_16_8_4_3_1_3146 8 36 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 131 (accept_3_2 7 36 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 36 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 131
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 131 (accept_3_2 4 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  131 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 131 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 36 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 131 (accept_3_2 1 36 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 131)))))))))))))))))))))))))))))))))))) (allB_succ 35 131 (allA_succ_of_accept 34 35 131
  (accept_3_2 34 35 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 131
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 35 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 131 (Polychromatic418967fa.accept_13_6_9_1_1_5604 32 35 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 131 (accept_3_2 31 35 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 35 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  35 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 131 (accept_3_2 28 35
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 131
  (Polychromatic418967fa.accept_19_8_16_17_1_6552 27 35 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 131 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 35 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 131 (accept_3_2 25 35 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 131 (Polychromatic418967fa.accept_11_1_2_10_1_1426
  23 35 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 131 (accept_3_2 22
  35 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 131
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 35 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 35 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 131 (accept_3_2 19 35 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 131 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 35 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 131 (Polychromatic418967fa.accept_15_2_5_11_1_1563
  17 35 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 131 (accept_3_2 16
  35 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 131
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 35 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 131 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 35 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 131 (accept_3_2 13 35 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  35 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 131 (accept_3_2 10 35
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 131
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 35 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 131 (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 35 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 131 (accept_3_2 7 35 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 35 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 131 (Polychromatic418967fa.accept_13_5_9_1_1_1405 5
  35 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 131 (accept_3_2 4 35 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 35
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 131
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 35 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 131 (accept_3_2 1 35 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  131))))))))))))))))))))))))))))))))))) (allB_succ 34 131 (allA_of_3_0 34 34 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 131 (allA_succ_of_accept 32 33 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 131 (accept_3_2 31 33 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  33 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 131
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 131 (accept_3_2 28 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 131 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 131 (accept_3_2 25 33 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 131 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 33 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 131
  (Polychromatic418967fa.accept_15_8_3_11_1_849 23 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 131 (accept_3_2 22 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 131 (accept_3_2 19 33 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 131
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 131 (accept_3_2 16 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 131 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 131 (accept_3_2 13 33 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 131
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 131 (accept_3_2 10 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 131 (Polychromatic418967fa.accept_18_9_15_5_1_6551 9 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 131 (accept_3_2 7 33 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 131
  (Polychromatic418967fa.accept_19_5_14_17_1_6550 5 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 131 (accept_3_2 4 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  131 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 33 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 131 (accept_3_2 1 33 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 131))))))))))))))))))))))))))))))))) (allB_succ 32 131 (allA_succ_of_accept 31 32 131
  (accept_3_2 31 32 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 131
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 32 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 32 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 131 (accept_3_2 28 32 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 131 (Polychromatic418967fa.accept_10_6_2_1_1_494
  26 32 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 131 (accept_3_2 25
  32 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 131
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 24 32 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 32 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 131 (accept_3_2 22 32 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 20
  32 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 131 (accept_3_2 19 32
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 131
  (Polychromatic418967fa.accept_13_5_6_1_1_822 18 32 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 32 131 (Polychromatic418967fa.accept_21_17_11_5_1_5060 17 32 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 131 (accept_3_2 16 32 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 32 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 131 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 32 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 131 (accept_3_2 13
  32 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 131
  (Polychromatic418967fa.accept_21_12_11_5_1_6549 12 32 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 32 131 (Polychromatic418967fa.accept_18_11_14_5_1_3951 11 32 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 131 (accept_3_2 10 32 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 32 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 32
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 131 (accept_3_2 7 32 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 131 (Polychromatic418967fa.accept_7_6_4_5_1_314 6
  32 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 131
  (Polychromatic418967fa.accept_13_5_6_1_1_822 5 32 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 131 (accept_3_2 4 32 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 32 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 131 (accept_3_2 1 32 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 131)))))))))))))))))))))))))))))))) (allB_succ 31 131 (allA_of_3_0 31 31 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 131 (allA_succ_of_accept 29 30 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 131 (accept_3_2 28 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 131 (Polychromatic418967fa.accept_16_11_14_3_1_3140 27 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 30 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 131 (accept_3_2 25 30 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 30 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 131
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 131 (accept_3_2 22 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 30 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 131 (accept_3_2 19 30 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 30 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 131 (accept_3_2 16 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 131 (Polychromatic418967fa.accept_19_14_11_17_1_6548 14 30 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 131 (accept_3_2 13 30 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 131 (Polychromatic418967fa.accept_21_12_9_5_1_6547 12 30
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 131
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 131 (accept_3_2 10 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 30 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 131 (accept_3_2 7 30 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 30 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 30 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 131 (accept_3_2 4 30 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  30 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 131
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 131 (accept_3_2 1 30 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  131)))))))))))))))))))))))))))))) (allB_succ 29 131 (allA_succ_of_accept 28 29 131 (accept_3_2 28 29 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 131 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 29 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 131 (accept_3_2 25 29 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 29 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 131 (Polychromatic418967fa.accept_19_4_10_17_1_5194 23 29 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 131 (accept_3_2 22 29 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 29 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 131
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 29 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 131 (accept_3_2 19 29 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 29 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 131 (accept_3_2 16 29 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 29 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 131 (accept_3_2 13 29 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 29 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 29 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 131 (accept_3_2 10 29 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 131 (Polychromatic418967fa.accept_23_9_6_16_1_6546 9 29 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 131
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 131 (accept_3_2 7 29 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 131 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 29 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 131 (accept_3_2 4 29 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 29 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 131 (accept_3_2 1 29 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 131))))))))))))))))))))))))))))) (allB_succ 28 131 (allA_of_3_0
  28 28 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 131 (allA_succ_of_accept 26 27 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 131 (accept_3_2 25 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 131 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 131 (Polychromatic418967fa.accept_15_8_12_11_1_1570 23 27 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 131 (accept_3_2 22 27 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 27
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 131 (accept_3_2 19 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 131 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 27 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 131 (accept_3_2 16 27 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 131 (accept_3_2 13 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 131 (Polychromatic418967fa.accept_18_12_9_5_1_2771 12 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 27 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 131 (accept_3_2 10 27 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 131 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 27 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 131 (accept_3_2 7 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  131 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 27 131 (Polychromatic418967fa.accept_17_5_10_12_1_6545 5 27 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 131 (accept_3_2 4 27 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 131 (Polychromatic418967fa.accept_19_3_8_17_1_5213 3 27 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 131 (accept_3_2 1 27 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27
  131))))))))))))))))))))))))))) (allB_succ 26 131 (allA_succ_of_accept 25 26 131 (accept_3_2 25 26 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 26 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 131
  (Polychromatic418967fa.accept_16_7_10_3_1_2210 23 26 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 131 (accept_3_2 22 26 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  26 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 26 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 26 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 131 (accept_3_2 19 26 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 131 (Polychromatic418967fa.accept_19_18_7_17_1_6544 18 26 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 26 131 (accept_3_2 16 26 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  26 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 26 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 26 131 (Polychromatic418967fa.accept_17_14_9_12_1_5350 14 26 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 131 (accept_3_2 13 26 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 26 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 131
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 26 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 131 (accept_3_2 10 26 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 131 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 26 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 131 (accept_3_2 7 26 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 131 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 26 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 131 (accept_3_2 4 26 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 131
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 26 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 131 (accept_3_2 1 26 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  131)))))))))))))))))))))))))) (allB_succ 25 131 (allA_of_3_0 25 25 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 131 (allA_succ_of_accept 23 24 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 131 (accept_3_2 22 24 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 131
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 24 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 131 (accept_3_2 19 24 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 131 (Polychromatic418967fa.accept_19_18_5_17_1_6543 18 24 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 131 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 131 (accept_3_2 16 24 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 131 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 131
  (Polychromatic418967fa.accept_19_14_5_17_1_6542 14 24 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 131 (accept_3_2 13 24 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 24 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 131 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 131 (accept_3_2 10 24 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 131 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 131
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 24 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 131 (accept_3_2 7 24 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  131 (Polychromatic418967fa.accept_15_6_9_11_1_858 6 24 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 24 131 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 24 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 131 (accept_3_2 4 24 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 131 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 131
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 24 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 131 (accept_3_2 1 24 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  131)))))))))))))))))))))))) (allB_succ 23 131 (allA_succ_of_accept 22 23 131 (accept_3_2 22 23 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 131 (Polychromatic418967fa.accept_14_7_9_5_1_529 21 23 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 131
  (Polychromatic418967fa.accept_8_4_7_3_1_144 20 23 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 131 (accept_3_2 19 23 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 23 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 23 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 131 (accept_3_2 16 23 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 131 (Polychromatic418967fa.accept_16_15_7_3_1_4273 15 23 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 131
  (Polychromatic418967fa.accept_20_14_3_11_1_6541 14 23 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 131 (accept_3_2 13 23 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 23 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 131 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 23 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 131 (accept_3_2 10 23 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 131 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 23 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 131
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 23 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 131 (accept_3_2 7 23 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  131 (Polychromatic418967fa.accept_19_6_4_17_1_6540 6 23 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 23 131 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 23 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 131 (accept_3_2 4 23 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 23 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 131
  (Polychromatic418967fa.accept_10_2_3_1_1_481 2 23 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 131 (accept_3_2 1 23 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  131))))))))))))))))))))))) (allB_succ 22 131 (allA_of_3_0 22 22 131 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 21 131 (allA_succ_of_accept 20 21 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 131 (accept_3_2 19 21 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 131
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 21 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 131 (accept_3_2 16 21 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 131 (accept_3_2 13 21 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 131 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 21 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 131
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 21 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 131 (accept_3_2 10 21 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 131 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 21 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 131 (accept_3_2 7 21 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 131
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 21 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 131 (accept_3_2 4 21 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  131 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 21 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 131 (accept_3_2 1 21 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 131))))))))))))))))))))) (allB_succ 20 131 (allA_succ_of_accept 19 20 131
  (accept_3_2 19 20 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 131
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 20 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 131 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 20 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 131 (accept_3_2 16 20 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 131 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 20 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 131 (accept_3_2 13
  20 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 131
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 20 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 131 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 20 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 131 (accept_3_2 10 20 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 131 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 20
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 131 (accept_3_2 7 20 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 131 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  20 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 131
  (Polychromatic418967fa.accept_22_5_20_21_1_6539 5 20 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 131 (accept_3_2 4 20 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 131 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 20 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 131 (accept_3_2 1 20 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 131)))))))))))))))))))) (allB_succ 19 131 (allA_of_3_0 19 19 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 131 (allA_succ_of_accept 17 18 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 131 (accept_3_2 16 18 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 131 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  18 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 131
  (Polychromatic418967fa.accept_11_3_7_10_1_180 14 18 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 131 (accept_3_2 13 18 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 131 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 18 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 131 (Polychromatic418967fa.accept_19_11_18_17_1_6538 11 18 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 131 (accept_3_2 10 18 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 131
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 18 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 131 (accept_3_2 7 18 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  131 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 18 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 131 (accept_3_2 4 18 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 131 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 18 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  18 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 131 (accept_3_2 1 18 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 131)))))))))))))))))) (allB_succ 17 131 (allA_succ_of_accept 16
  17 131 (accept_3_2 16 17 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 131
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 17 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 131 (accept_3_2 13 17 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 17 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  17 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 131 (accept_3_2 10 17
  131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 131 (Polychromatic418967fa.accept_7_2_3_5_1_34
  9 17 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 131
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 17 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 131 (accept_3_2 7 17 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  131 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 131 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 17 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 131 (accept_3_2 4 17 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 131 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 17 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 131 (accept_3_2 1 17 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 131))))))))))))))))) (allB_succ 16 131 (allA_of_3_0 16 16 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 131 (allA_succ_of_accept 14 15 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 131 (accept_3_2 13 15 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 131 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 15 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 131 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 15 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 131 (accept_3_2 10 15 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 131 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 15 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 131 (accept_3_2 7 15 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  131 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 15 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 131 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 15 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 131 (accept_3_2 4 15 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 131 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 131 (accept_3_2 1 15 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 131))))))))))))))) (allB_succ 14 131 (allA_succ_of_accept 13 14
  131 (accept_3_2 13 14 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 131
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 12 14 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 14 131 (Polychromatic418967fa.accept_16_11_14_3_1_3140 11 14 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 131 (accept_3_2 10 14 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 131
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 14 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 14 131 (accept_3_2 7 14 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14
  131 (Polychromatic418967fa.accept_20_6_14_11_1_6537 6 14 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 14 131 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 131 (accept_3_2 4 14 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 131
  (Polychromatic418967fa.accept_19_2_14_17_1_700 2 14 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 131 (accept_3_2 1 14 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  131)))))))))))))) (allB_succ 13 131 (allA_of_3_0 13 13 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 131
  (allA_succ_of_accept 11 12 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 12 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 131 (accept_3_2 10 12 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 131 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 12 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 131 (Polychromatic418967fa.accept_9_8_3_5_1_241 8
  12 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 131 (accept_3_2 7 12 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 131 (Polychromatic418967fa.accept_9_6_3_5_1_240 6
  12 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 131
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 12 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 12 131 (accept_3_2 4 12 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12
  131 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 12 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 131 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 12 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 131 (accept_3_2 1 12 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 131)))))))))))) (allB_succ 11 131 (allA_succ_of_accept 10 11 131 (accept_3_2 10 11 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 9
  11 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 131
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 11 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 131 (accept_3_2 7 11 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  131 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 11 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 131 (Polychromatic418967fa.accept_19_5_11_17_1_6536 5 11 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 131 (accept_3_2 4 11 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 131 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 11 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 131 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  11 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 131 (accept_3_2 1 11 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 131))))))))))) (allB_succ 10 131 (allA_of_3_0 10 10 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 9 131 (allA_succ_of_accept 8 9 131
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 131 (accept_3_2 7 9 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 131 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 9 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 131 (accept_3_2 4 9 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 131 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 9 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 131 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 131 (accept_3_2 1 9 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 131))))))))) (allB_succ 8 131 (allA_succ_of_accept 7 8 131
  (accept_3_2 7 8 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 131
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 8 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 131 (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 8 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 131 (accept_3_2 4 8 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 131 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 131 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 131 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 8
  131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 131 (accept_3_2 1 8 131
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 131)))))))) (allB_succ 7 131 (allA_of_3_0 7 7 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 6 131 (allA_succ_of_accept 5 6 131
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 131 (accept_3_2 4 6 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 131
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 6 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 131 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 6 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 131 (accept_3_2 1 6 131 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 131)))))) (allB_succ 5 131 (allA_succ_of_accept 4 5 131 (accept_3_2 4 5 131 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 131 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 5 131
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 131
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 131 (accept_3_2 1 5 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 131)))))
  (allB_succ 4 131 (allA_of_3_0 4 4 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 131 (allA_succ_of_accept 2
  3 131 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 131 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 131 (accept_3_2 1 3 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 131)))
  (allB_succ 2 131 (allA_succ_of_accept 1 2 131 (accept_3_2 1 2 131 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  131)) (allB_two
  131)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


