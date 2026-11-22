-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch135
-- name    : Polychromatic418967fa_Branch135
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:14:41.59571+00:00
-- url     : https://prove2.me/theorems/0f07b147-0d8a-4cdb-8dd2-f6ad9c8c9694
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

def Polychromatic418967fa.branch_135 : allB 135 135 :=
  allB_succ' 2 134 135 (Eq.refl Bool.true) (allA_succ_of_accept 1 134 135 (accept_3_4 1 134 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 134 135)) (allB_succ' 3 133 135 (Eq.refl Bool.true) (allA_succ_of_accept 2 133 135
  (accept_3_5 2 133 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 135
  (Polychromatic418967fa.accept_13_1_3_5_1_140 1 133 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 133 135))) (allB_succ' 4 132 135 (Eq.refl Bool.true) (allA_succ_of_gcd 3 132 135 3 1 44 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 132 135
  (Polychromatic418967fa.accept_18_2_6_9_1_1032 2 132 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 132 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132 135)))) (allB_succ' 5 131 135 (Eq.refl Bool.true) (allA_succ_of_accept 4
  131 135 (accept_3_4 4 131 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 131 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 131 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 131 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 135 (accept_3_4 1 131 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 131 135))))) (allB_succ' 6 130 135 (Eq.refl Bool.true) (allA_succ_of_gcd 5 130 135 5 1 26 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 130 135
  (Polychromatic418967fa.accept_19_4_16_2_1_6967 4 130 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 130 135 (Polychromatic418967fa.accept_19_3_16_2_1_6837 3 130 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 135 (accept_3_5 2 130 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 130 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 135)))))) (allB_succ' 7 129 135 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 129 135 3 2 43 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 129 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 129 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 135 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 129 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 135 3 1 43 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 129 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 129 135))))))) (allB_succ' 8 128 135 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 128 135 (accept_3_4 7 128 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 135 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 128 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 135 (accept_3_4 4 128 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 135 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 128 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 135
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 128 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 135 (accept_3_4 1 128 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  135)))))))) (allB_succ' 9 127 135 (Eq.refl Bool.true) (allA_succ_of_accept 8 127 135 (accept_3_5 8 127 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 135 (Polychromatic418967fa.accept_17_7_8_16_1_6966 7 127
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 127 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 135 (accept_3_5 5 127 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 127 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 135 (accept_3_5 2 127 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 135 (Polychromatic418967fa.accept_19_1_13_2_1_6923 1 127 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 135))))))))) (allB_succ' 10 126 135 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 126 135 9 1 14 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 126 135 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 126 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 135 (Polychromatic418967fa.accept_22_7_16_3_1_6965
  7 126 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 135 3 2 42 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 126 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 126 135 3 1 42 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 126 135 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 126 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 135)))))))))) (allB_succ' 11 125 135 (Eq.refl Bool.true) (allA_succ_of_gcd 10 125 135 5 2 25 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 125 135
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 125 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 125 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 125 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 135 (accept_3_4 7 125 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 125 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 125 135 5 1 25 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 125 135 (accept_3_4 4 125 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 125 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 135 (accept_3_4 1 125 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  135))))))))))) (allB_succ' 12 124 135 (Eq.refl Bool.true) (allA_succ_of_accept 11 124 135 (accept_3_5 11 124 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 10
  124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 135
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 135 (accept_3_5 8 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 124 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 135 (accept_3_5 5 124 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 124 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 135 (accept_3_5 2 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124 135)))))))))))) (allB_succ' 13 123 135 (Eq.refl Bool.true) (allA_succ_of_gcd 12 123 135 3 4
  41 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 135
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 123 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 135 (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 123 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 135 3 3 41 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 135 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 123 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 135
  (Polychromatic418967fa.accept_10_7_3_5_1_301 7 123 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 123 135 3 2 41 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 123 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 123 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 135 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 123 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 135 3 1 41 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 135
  (Polychromatic418967fa.accept_10_2_3_5_1_996 2 123 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 135 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 123 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 123 135))))))))))))) (allB_succ' 14 122 135 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 122 135 (accept_3_4 13 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 122 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 135 (accept_3_4 10 122 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 135 (accept_3_4 7 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 135 (accept_3_4 4 122 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 135 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 122 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 135
  (Polychromatic418967fa.accept_11_2_1_3_1_683 2 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 135 (accept_3_4 1 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  135)))))))))))))) (allB_succ' 15 121 135 (Eq.refl Bool.true) (allA_succ_of_accept 14 121 135 (accept_3_5 14 121 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 135
  (Polychromatic418967fa.accept_16_13_9_7_1_4532 13 121 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 121 135 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 121 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 135 (accept_3_5 11 121 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 121 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  121 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 135 (accept_3_5 8 121
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 135
  (Polychromatic418967fa.accept_20_7_1_15_1_2700 7 121 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 121 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 135 (accept_3_5 5 121 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 121 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 121 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 135 (Polychromatic418967fa.accept_16_3_9_7_1_6842
  3 121 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 135 (accept_3_5 2
  121 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 135
  (Polychromatic418967fa.accept_13_1_4_5_1_113 1 121 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 121 135))))))))))))))) (allB_succ' 16 120 135 (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 135 15 1 8 9
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 135
  (Polychromatic418967fa.accept_13_1_3_5_1_140 14 120 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 120 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 135 3 4 40 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 135 (Polychromatic418967fa.accept_13_11_3_5_1_982
  11 120 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 135 5 2 24 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 120 135 3 3 40 45
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 120 135
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 8 120 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 135 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 120 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 135 3 2 40 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 120 135 5 1 24 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 120 135 (Polychromatic418967fa.accept_16_4_8_7_1_3396 4 120 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 120 135 3 1 40 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 120 135
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 2 120 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 135 (Polychromatic418967fa.accept_13_1_3_5_1_140 1 120 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120 135)))))))))))))))) (allB_succ' 17 119 135 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 119 135 (accept_3_4 16 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 135 (Polychromatic418967fa.accept_18_15_11_9_1_4256 15 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 119 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 135 (accept_3_4 13 119 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 135 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 119 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 135
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 135 (accept_3_4 10 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 119 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 135 (accept_3_4 7 119 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 135 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 119 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 135
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 5 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 135 (accept_3_4 4 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 135 (Polychromatic418967fa.accept_13_3_2_5_1_1632 3 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 119 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 135 (accept_3_4 1 119 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119 135))))))))))))))))) (allB_succ' 18 118 135 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 135 (accept_3_5 17 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 135 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 118 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 135 (accept_3_5 14 118 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 135
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 135 (accept_3_5 11 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 135 (accept_3_5 8 118 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 118 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 135
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 135 (accept_3_5 5 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 118 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 135 (accept_3_5 2 118 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 135)))))))))))))))))) (allB_succ' 19 117 135
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 117 135 9 2 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 117 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 117 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 135
  (Polychromatic418967fa.accept_19_16_3_2_1_6964 16 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 117 135 3 5 39 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 117 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 117
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 135 3 4 39 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 135
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 135 9 1 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 135 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 117 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 135
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 117 135 3 2 39 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 117 135 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 117 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 117 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 135 3 1 39 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 135 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 117 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117 135))))))))))))))))))) (allB_succ' 20 116 135 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 135 (accept_3_4 19 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 116 135 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 116 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 116 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 135 (accept_3_4 16 116 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 116 135 (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 116 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 135
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 116 135 (accept_3_4 13 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 116 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 116 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 116 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 135 (accept_3_4 10 116 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 135 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 116 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 135
  (Polychromatic418967fa.accept_11_8_6_3_1_661 8 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 135 (accept_3_4 7 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 135 (accept_3_4 4 116 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 116 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 135
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 2 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 135 (accept_3_4 1 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  135)))))))))))))))))))) (allB_succ' 21 115 135 (Eq.refl Bool.true) (allA_succ_of_gcd 20 115 135 5 4 23 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 115 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 135 (Polychromatic418967fa.accept_19_18_1_2_1_5430 18 115 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 135 (accept_3_5 17 115 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 115 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 115 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 115 135 5 3 23 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 115 135 (accept_3_5 14 115 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 115 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 135 (accept_3_5 11 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  115 135 5 2 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 115 135 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 115 135 (accept_3_5 8 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 115 135 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 115 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 115 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 115 135 5 1 23 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 115 135
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 115 135 (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 115 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 135 (accept_3_5 2 115 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 115 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 115 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 135))))))))))))))))))))) (allB_succ' 22 114 135 (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 114 135 3 7 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 114 135 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 114 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 135 (Polychromatic418967fa.accept_10_9_4_5_1_616
  19 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 114 135 3 6 38 45
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 114 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 114 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 114 135 3 5 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 114 135 (Polychromatic418967fa.accept_12_2_6_3_1_331
  14 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 135 3 4 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 114 135 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 114 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 135 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 114
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 114 135 3 3 38 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 114 135
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 135 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 114 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 135 3 2 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 135
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 114 135 3 1 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 114 135 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 114 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 135)))))))))))))))))))))) (allB_succ' 23
  113 135 (Eq.refl Bool.true) (allA_succ_of_accept 22 113 135 (accept_3_4 22 113 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 113 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 113 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 135 (accept_3_4 19 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 113 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 135 (accept_3_4 16 113 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 135 (Polychromatic418967fa.accept_13_2_9_5_1_959 15 113 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 135 (accept_3_4 13 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 135 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 135 (Polychromatic418967fa.accept_20_11_13_15_1_6931 11 113 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 135 (accept_3_4 10 113 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 113 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 135 (accept_3_4 7 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 135 (Polychromatic418967fa.accept_17_5_11_16_1_3257 5 113 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 135 (accept_3_4 4 113 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 113 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 135 (accept_3_4 1 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  135))))))))))))))))))))))) (allB_succ' 24 112 135 (Eq.refl Bool.true) (allA_succ_of_accept 23 112 135 (accept_3_5 23
  112 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 135
  (Polychromatic418967fa.accept_19_3_17_2_1_6963 22 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 112 135 (Polychromatic418967fa.accept_22_21_2_3_1_6962 21 112 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 112 135 (accept_3_5 20 112 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 112 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 112 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 135 (Polychromatic418967fa.accept_10_8_2_5_1_596
  18 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 135 (accept_3_5 17
  112 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 135
  (Polychromatic418967fa.accept_13_3_8_5_1_974 16 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 112 135 (Polychromatic418967fa.accept_18_15_4_9_1_4204 15 112 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 135 (accept_3_5 14 112 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 112 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 112 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 135 (Polychromatic418967fa.accept_11_1_2_3_1_688
  12 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 135 (accept_3_5 11
  112 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 135
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 112 135 (Polychromatic418967fa.accept_17_9_10_16_1_3217 9 112 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 135 (accept_3_5 8 112 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 112 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 112 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 135 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 135 (accept_3_5 5 112
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 135
  (Polychromatic418967fa.accept_19_4_17_2_1_5409 4 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 112 135 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 112 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 135 (accept_3_5 2 112 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 112 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 135)))))))))))))))))))))))) (allB_succ' 25 111 135 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 111 135 3 8 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 111 135 (Polychromatic418967fa.accept_17_6_9_16_1_4410 23 111 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 22 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 111 135 3 7 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 111 135 (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 111 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 111
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 135 3 6 37 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 135
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 135 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 111 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 135 3 5 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 135 (Polychromatic418967fa.accept_10_4_1_5_1_1018
  14 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 135
  (Polychromatic418967fa.accept_11_2_1_3_1_683 13 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 111 135 3 4 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 111 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 111 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 111 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 135 3 3 37 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 135 (Polychromatic418967fa.accept_18_7_3_9_1_1020 7 111 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 135 3 2 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 135 (Polychromatic418967fa.accept_19_5_16_2_1_1717 5 111 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 135
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 111 135 3 1 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 111 135 (Polychromatic418967fa.accept_11_2_1_3_1_683 2 111 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 111 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111 135))))))))))))))))))))))))) (allB_succ' 26
  110 135 (Eq.refl Bool.true) (allA_succ_of_gcd 25 110 135 5 5 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 110 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 110 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 135
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 110 135 (accept_3_4 22 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 110 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 110 135 5 4 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 110 135 (accept_3_4 19 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 110 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 110 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 135 (accept_3_4 16 110 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 110 135 5 3 22 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 110 135
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 110 135 (accept_3_4 13 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 110 135 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 110 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 110 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 135 5 2 22 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 110 135 (Polychromatic418967fa.accept_19_8_15_2_1_6961 8 110 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 135 (accept_3_4 7 110 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 110 135 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 110 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 110 135 5 1 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 110 135 (accept_3_4 4 110 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 110 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 135
  (Polychromatic418967fa.accept_17_2_8_16_1_4403 2 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 135 (accept_3_4 1 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  135)))))))))))))))))))))))))) (allB_succ' 27 109 135 (Eq.refl Bool.true) (allA_succ_of_accept 26 109 135 (accept_3_5
  26 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 135
  (Polychromatic418967fa.accept_16_9_13_7_1_1509 25 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 109 135 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 109 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 135 (accept_3_5 23 109 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 109 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 135 (Polychromatic418967fa.accept_10_1_9_5_1_83
  21 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 135 (accept_3_5 20
  109 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 135
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 109 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 135 (accept_3_5 17 109 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 109 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 109 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 135
  (Polychromatic418967fa.accept_21_15_4_9_1_5340 15 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 135 (accept_3_5 14 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 109 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 135 (accept_3_5 11 109 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 135
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 135 (accept_3_5 8 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 135 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 135 (accept_3_5 5 109 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 135
  (Polychromatic418967fa.accept_17_3_7_16_1_3251 3 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 135 (accept_3_5 2 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 135))))))))))))))))))))))))))) (allB_succ' 28 108 135 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 108 135 27 1 4 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 108 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 108 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 135 (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 108
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 135 3 8 36 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 135
  (Polychromatic418967fa.accept_10_3_8_5_1_606 23 108 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 108 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 108 135 3 7 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 108 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 20
  108 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 108 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 135 9 2 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 135 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 108 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 135 (Polychromatic418967fa.accept_19_16_13_2_1_6920 16 108
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 108 135 3 5 36 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 108 135
  (Polychromatic418967fa.accept_13_1_4_5_1_113 14 108 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 108 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 135 3 4 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 11
  108 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 135
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 108 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 108 135 9 1 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 108 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 108 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 135 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 108 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 135 3 2 36 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 108 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 135 (Polychromatic418967fa.accept_16_4_12_7_1_4475 4 108 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 108 135 3 1 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 108 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 108 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 108 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 135)))))))))))))))))))))))))))) (allB_succ' 29 107 135 (Eq.refl Bool.true) (allA_succ_of_accept 28 107
  135 (accept_3_4 28 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 135
  (Polychromatic418967fa.accept_11_5_8_3_1_66 27 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 107 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 107 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 135 (accept_3_4 25 107 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 107 135 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 107 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 135
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 135 (accept_3_4 22 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 135 (accept_3_4 19 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 135 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 107 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 135
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 135 (accept_3_4 16 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 135 (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 135 (accept_3_4 13 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 135 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 107 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 135
  (Polychromatic418967fa.accept_13_11_3_5_1_982 11 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 135 (accept_3_4 10 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 135 (accept_3_4 7 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 135 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 107 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 135
  (Polychromatic418967fa.accept_11_5_8_3_1_66 5 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 135 (accept_3_4 4 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 135 (accept_3_4 1 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 135))))))))))))))))))))))))))))) (allB_succ' 30 106 135 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 106 135 (accept_3_5 29 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 135 (Polychromatic418967fa.accept_19_9_11_2_1_5436 28 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 135 (accept_3_5 26 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 135
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 135 (accept_3_5 23 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 135 (Polychromatic418967fa.accept_13_9_2_5_1_2310 22 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 135 (accept_3_5 20 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 106 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 135
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 135 (accept_3_5 17 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 135 (Polychromatic418967fa.accept_13_3_2_5_1_1632 16 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 135 (Polychromatic418967fa.accept_11_4_7_3_1_289 15 106 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 135 (accept_3_5 14 106 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 135
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 135 (accept_3_5 11 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 135 (accept_3_5 8 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 106 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 135 (accept_3_5 5 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 135 (accept_3_5 2 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 135)))))))))))))))))))))))))))))) (allB_succ' 31 105
  135 (Eq.refl Bool.true) (allA_succ_of_gcd 30 105 135 15 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 135 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 105 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 135
  (Polychromatic418967fa.accept_18_10_15_9_1_1054 28 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 105 135 3 9 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 105 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 105 135 5 5 21 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 105 135 3 8 35 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 135
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 135 3 7 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 105 135 5 4 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 135 (Polychromatic418967fa.accept_11_8_6_3_1_661
  19 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 135 3 6 35 45
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 135
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 135 (Polychromatic418967fa.accept_13_3_1_5_1_499 16 105 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 135 15 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 135
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 105 135 3 4 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 105 135 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 105 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 135 5 2 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 105 135 3 3 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 135 (Polychromatic418967fa.accept_11_8_6_3_1_661 8
  105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 135
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 105 135 3 2 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 105 135 5 1 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 105 135 (Polychromatic418967fa.accept_13_4_1_5_1_1628 4 105 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 135 3 1 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 135
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 105 135))))))))))))))))))))))))))))))) (allB_succ' 32 104 135 (Eq.refl Bool.true) (allA_succ_of_accept 31
  104 135 (accept_3_4 31 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 135
  (Polychromatic418967fa.accept_11_8_5_3_1_694 30 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 104 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 104 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 135 (accept_3_4 28 104 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 104 135 (Polychromatic418967fa.accept_21_6_20_9_1_6943 27 104 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 135
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 135 (accept_3_4 25 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 104 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 135 (accept_3_4 22 104 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 135 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 104 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 135
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 20 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 135 (accept_3_4 19 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 104 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 135 (accept_3_4 16 104 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 104 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 135
  (Polychromatic418967fa.accept_17_14_2_16_1_4380 14 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 104 135 (accept_3_4 13 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 104 135 (Polychromatic418967fa.accept_16_12_8_7_1_4530 12 104 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 104 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 135 (accept_3_4 10 104 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 135 (Polychromatic418967fa.accept_10_9_4_5_1_616 9
  104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 135 (accept_3_4 7 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 135 (accept_3_4 4 104 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 104 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 135
  (Polychromatic418967fa.accept_20_2_4_15_1_6911 2 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 135 (accept_3_4 1 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  135)))))))))))))))))))))))))))))))) (allB_succ' 33 103 135 (Eq.refl Bool.true) (allA_succ_of_accept 32 103 135
  (accept_3_5 32 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 103 135 (Polychromatic418967fa.accept_13_4_12_5_1_476 30 103 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 135 (accept_3_5 29 103 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 103 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 103 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 135 (Polychromatic418967fa.accept_10_7_3_5_1_301
  27 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 135 (accept_3_5 26
  103 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 135
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 103 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 103 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 135 (accept_3_5 23 103 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 103 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 103 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 135 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  21 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 135 (accept_3_5 20
  103 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 135
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 19 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 103 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 103 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 135 (accept_3_5 17 103 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 103 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 103 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 135
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 135 (accept_3_5 14 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 135 (Polychromatic418967fa.accept_19_13_8_2_1_4089 13 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 135 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 103 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 135 (accept_3_5 11 103 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 103 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 135
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 135 (accept_3_5 8 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 135 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 135 (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 103 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 135 (accept_3_5 5 103 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 135 (accept_3_5 2 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 135 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 135))))))))))))))))))))))))))))))))) (allB_succ' 34 102 135 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 102 135 3 11 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 102 135 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 102 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 135
  (Polychromatic418967fa.accept_16_15_6_7_1_4512 31 102 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 135 3 10 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 135 (Polychromatic418967fa.accept_10_8_2_5_1_596
  28 102 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 102 135 3 9 34 45
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 102 135
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 102 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 102 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 102 135 3 8 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 102 135 (Polychromatic418967fa.accept_10_3_2_5_1_295
  23 102 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 135
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 102 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 102 135 3 7 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 102 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 102 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 102 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 102 135 3 6 34 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 102 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 135 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 102 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 102 135 3 5 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 102 135 (Polychromatic418967fa.accept_12_2_6_3_1_331
  14 102 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 135 3 4 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 102 135 (Polychromatic418967fa.accept_18_11_12_9_1_992 11 102 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 135 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 102
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 102 135 3 3 34 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 102 135
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 102 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 135 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 102 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 135 3 2 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 135
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 102 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 102 135 3 1 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 102 135 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 102 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 135))))))))))))))))))))))))))))))))))
  (allB_succ' 35 101 135 (Eq.refl Bool.true) (allA_succ_of_accept 34 101 135 (accept_3_4 34 101 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 101 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 135 (accept_3_4 31 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 101 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 135 (accept_3_4 28 101 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 101 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 135 (accept_3_4 25 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 135 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 135 (Polychromatic418967fa.accept_11_1_2_3_1_688 23 101 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 135 (accept_3_4 22 101 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 101
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 135 (accept_3_4 19 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 135 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 101 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 135 (accept_3_4 16 101 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 101 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 135 (accept_3_4 13 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 135 (Polychromatic418967fa.accept_16_11_5_7_1_2395 11 101 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 135 (accept_3_4 10 101 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 101 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 135 (accept_3_4 7 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 135 (accept_3_4 4 101 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 135 (Polychromatic418967fa.accept_19_3_6_2_1_6910 3 101 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 135 (accept_3_4 1 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  135))))))))))))))))))))))))))))))))))) (allB_succ' 36 100 135 (Eq.refl Bool.true) (allA_succ_of_gcd 35 100 135 5 7 20
  27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 100 135
  (Polychromatic418967fa.accept_21_13_16_9_1_2541 34 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 100 135 (Polychromatic418967fa.accept_18_15_10_9_1_2009 33 100 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 135 (accept_3_5 32 100 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 100 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 100 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 135 5 6 20 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 135 (accept_3_5 29
  100 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 135
  (Polychromatic418967fa.accept_13_2_9_5_1_959 28 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 100 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 100 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 100 135 (accept_3_5 26 100 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 100 135 5 5 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 100 135 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 100 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 135 (accept_3_5 23 100 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 135 (Polychromatic418967fa.accept_19_3_5_2_1_4103 22 100
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 135
  (Polychromatic418967fa.accept_14_7_2_9_1_2093 21 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 135 5 4 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 100 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 100 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 100 135 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 100
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 135 (accept_3_5 17 100
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 135
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 16 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 100 135 5 3 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 100 135 (accept_3_5 14 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 135 (Polychromatic418967fa.accept_16_12_4_7_1_3391 12 100 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 135 (accept_3_5 11 100 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 135 5 2 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 135 (Polychromatic418967fa.accept_22_9_12_3_1_6960
  9 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 135 (accept_3_5 8
  100 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 100 135
  (Polychromatic418967fa.accept_6_1_4_3_1_14 7 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 100 135 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 100 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 100 135 5 1 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 100 135 (Polychromatic418967fa.accept_13_4_9_5_1_1641 4 100 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 135
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 135 (accept_3_5 2 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100 135)))))))))))))))))))))))))))))))))))) (allB_succ' 37 99 135 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 99 135 9 4 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 99 135 (Polychromatic418967fa.accept_19_16_4_2_1_4102 35 99 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 99 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99 135 3 11 33 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 99 135
  (Polychromatic418967fa.accept_17_15_14_16_1_5625 32 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 99 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 99 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 135 3 10 33 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 135
  (Polychromatic418967fa.accept_13_3_8_5_1_974 29 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 135 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 99 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 135 9 3 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 135 (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 99 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 135
  (Polychromatic418967fa.accept_13_12_8_5_1_976 25 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 135 3 8 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 135 (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 99 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 135 (Polychromatic418967fa.accept_14_8_1_9_1_2085 22 99 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 135 3 7 33 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 135 (Polychromatic418967fa.accept_17_2_14_16_1_2187 19 99 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 135 9 2 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 99 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 135
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 135 3 5 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 135 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 99 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 99 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 135 3 4 33 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 135
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 99 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 135 9 1 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 135 (Polychromatic418967fa.accept_14_8_1_9_1_2085 8 99 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 135
  (Polychromatic418967fa.accept_19_7_4_2_1_6959 7 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 135 3 2 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 135 (Polychromatic418967fa.accept_19_5_4_2_1_6840 5 99 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 135 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 99 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 135 3 1 33 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 135
  (Polychromatic418967fa.accept_17_2_14_16_1_2187 2 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 99 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99 135))))))))))))))))))))))))))))))))))))) (allB_succ' 38 98 135 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 98 135 (accept_3_4 37 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 98 135 (Polychromatic418967fa.accept_19_17_3_2_1_1725 36 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 98 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 98 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 135 (accept_3_4 34 98 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 135
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 135 (accept_3_4 31 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 135 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 135 (accept_3_4 28 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 135 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 98 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 135
  (Polychromatic418967fa.accept_17_9_13_16_1_3266 26 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 135 (accept_3_4 25 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 135 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 135 (accept_3_4 22 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 135
  (Polychromatic418967fa.accept_17_3_13_16_1_2183 20 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 135 (accept_3_4 19 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 135 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 135 (accept_3_4 16 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 135 (Polychromatic418967fa.accept_13_2_7_5_1_3189 15 98 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 135
  (Polychromatic418967fa.accept_23_14_6_20_1_6958 14 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 135 (accept_3_4 13 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 135 (accept_3_4 10 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 135
  (Polychromatic418967fa.accept_24_8_2_15_1_6933 8 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 135 (accept_3_4 7 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  135 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 135 (accept_3_4 4 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 135 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 135 (accept_3_4 1 98 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98 135)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 97 135
  (Eq.refl Bool.true) (allA_succ_of_accept 38 97 135 (accept_3_5 38 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 97 135 (Polychromatic418967fa.accept_13_11_6_5_1_2339 37 97 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 97 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 135 (accept_3_5 35 97 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 135
  (Polychromatic418967fa.accept_10_3_7_5_1_288 33 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 135 (accept_3_5 32 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 135 (accept_3_5 29 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 135
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 135 (accept_3_5 26 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 135 (accept_3_5 23 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 135
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 135 (accept_3_5 20 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 135 (Polychromatic418967fa.accept_20_19_17_15_1_2690 19 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 135 (accept_3_5 17 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 135 (accept_3_5 14 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 135 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 135 (accept_3_5 11 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 135
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 135 (accept_3_5 8 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  135 (Polychromatic418967fa.accept_21_7_13_9_1_6937 7 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 135 (accept_3_5 5 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 135
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 135 (accept_3_5 2 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  135 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 135))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 96 135 (Eq.refl Bool.true) (allA_succ_of_gcd 39
  96 135 3 13 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  38 96 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 96 135 (Polychromatic418967fa.accept_18_1_6_9_1_2001 37 96 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 135 3 12 32 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 135
  (Polychromatic418967fa.accept_14_7_12_9_1_2926 35 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 96 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 96 135 3 11 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 96 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 135 3 10 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 96 135 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 96 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 135 (Polychromatic418967fa.accept_11_6_8_3_1_2236 28 96 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 96 135 3 9 32 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 135
  (Polychromatic418967fa.accept_18_8_6_9_1_5576 26 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 96 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 135 3 8 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 135 (Polychromatic418967fa.accept_21_2_12_9_1_5324 23 96 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 135
  (Polychromatic418967fa.accept_17_5_11_16_1_3257 22 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 96 135 3 7 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 96 135 (Polychromatic418967fa.accept_18_2_6_9_1_1032 20 96 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 135 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 96 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 135 3 6 32 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 135 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 96 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 96 135 3 5 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 96 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 96 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 135
  (Polychromatic418967fa.accept_18_13_6_9_1_4280 13 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 135 3 4 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 96 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 135 3 3 32 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 135
  (Polychromatic418967fa.accept_18_8_6_9_1_5576 8 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 135 (Polychromatic418967fa.accept_14_7_12_9_1_2926 7 96 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 135 3 2 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 135 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 96 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 135
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 96 135 3 1 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 96 135 (Polychromatic418967fa.accept_18_2_6_9_1_1032 2 96 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 135 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 96 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 135))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 95 135 (Eq.refl Bool.true) (allA_succ_of_gcd 40 95 135 5 8 19 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 95 135
  (Polychromatic418967fa.accept_21_18_11_9_1_6956 39 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 95 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 135 (accept_3_4 37 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 95 135 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 95 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 95 135 5 7 19 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 95 135 (accept_3_4 34 95 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 95 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 135 (accept_3_4 31 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 95
  135 5 6 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  95 135 (Polychromatic418967fa.accept_23_6_3_20_1_6957 29 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 95 135 (accept_3_4 28 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 95 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 95 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 95 135 5 5 19 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 95 135
  (Polychromatic418967fa.accept_16_8_15_7_1_5658 24 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 95 135 (Polychromatic418967fa.accept_13_10_4_5_1_2331 23 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 135 (accept_3_4 22 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 95 135 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 95 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 135 5 4 19 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 135 (accept_3_4 19 95 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 135 (Polychromatic418967fa.accept_21_18_11_9_1_6956 18 95
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 135
  (Polychromatic418967fa.accept_23_17_3_20_1_6955 17 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 135 (accept_3_4 16 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 95
  135 5 3 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  95 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 95 135 (accept_3_4 13 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 95 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 135 (Polychromatic418967fa.accept_16_11_15_7_1_5654 11 95
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 95 135 5 2 19 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 95 135
  (Polychromatic418967fa.accept_12_9_11_3_1_772 9 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 95 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 135 (accept_3_4 7 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 95 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 95 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 135 5 1 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 135 (accept_3_4 4 95 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 135 (Polychromatic418967fa.accept_16_3_15_7_1_3417 3 95 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 135 (accept_3_4 1 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  135))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 94 135 (Eq.refl Bool.true) (allA_succ_of_accept 41 94 135
  (accept_3_5 41 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 94 135 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 135 (accept_3_5 38 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 94 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 36
  94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 135 (accept_3_5 35 94
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 94 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 135 (accept_3_5 32 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 94 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 135 (Polychromatic418967fa.accept_11_8_6_3_1_661
  30 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 135 (accept_3_5 29
  94 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 135
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 28 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 94 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 135 (accept_3_5 26 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 94 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 135 (Polychromatic418967fa.accept_13_11_3_5_1_982
  24 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 135 (accept_3_5 23
  94 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 22 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 94 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 135 (accept_3_5 20 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 94 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 135 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  18 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 135 (accept_3_5 17
  94 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 135
  (Polychromatic418967fa.accept_10_6_4_5_1_615 16 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 94 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 135 (accept_3_5 14 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 94 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 12
  94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 135 (accept_3_5 11 94
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 135
  (Polychromatic418967fa.accept_16_10_14_7_1_2372 10 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 94 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 135 (accept_3_5 8 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 94 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 135 (accept_3_5 5 94 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94 135 (Polychromatic418967fa.accept_16_4_14_7_1_5641
  4 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 135
  (Polychromatic418967fa.accept_19_3_18_2_1_6935 3 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 94 135 (accept_3_5 2 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94
  135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 135)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 93 135 (Eq.refl Bool.true) (allA_succ_of_gcd
  42 93 135 3 14 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 93 135 (Polychromatic418967fa.accept_11_8_5_3_1_694 41 93 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 135 (Polychromatic418967fa.accept_24_16_21_15_1_6954 40 93
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 93 135 3 13 31 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 93 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 135 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 93 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 135 3 12 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 135 (Polychromatic418967fa.accept_12_11_9_3_1_792
  35 93 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 93 135 3 11 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 93 135 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 93 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 135 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 93 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 135 3 10 31 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 135
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 93 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 135 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 93 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 135 3 9 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 135
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 93 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 93 135 3 8 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 93 135 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 93 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 135 3 7 31 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 135
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 20 93 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 135 (Polychromatic418967fa.accept_11_8_5_3_1_694 19 93 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 135 3 6 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 135 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 93 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 135
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 16 93 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 93 135 3 5 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 93 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 135 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 93 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 135 3 4 31 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 135
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 93 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 135 3 3 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 135 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 93 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 135
  (Polychromatic418967fa.accept_10_7_3_5_1_301 7 93 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 93 135 3 2 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 93 135 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 93 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 135 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 93 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 135 3 1 31 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 93 135 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 93 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 93 135))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 92 135
  (Eq.refl Bool.true) (allA_succ_of_accept 43 92 135 (accept_3_4 43 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 92 135 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 92 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 92 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 135 (accept_3_4 40 92 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 135 (Polychromatic418967fa.accept_18_3_2_9_1_1013
  39 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 135
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 135 (accept_3_4 37 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 135 (Polychromatic418967fa.accept_16_4_12_7_1_4475 36 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 135 (accept_3_4 34 92 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 135 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 92 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 135
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 32 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 135 (accept_3_4 31 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 135 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 135 (accept_3_4 28 92 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 92 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 135
  (Polychromatic418967fa.accept_19_7_16_2_1_6953 26 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 135 (accept_3_4 25 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 135 (accept_3_4 22 92 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 135 (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 92 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 135 (accept_3_4 19 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 135 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 135 (accept_3_4 16 92 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 135 (Polychromatic418967fa.accept_14_1_8_9_1_1312 15 92 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 135
  (Polychromatic418967fa.accept_19_14_16_2_1_6952 14 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 135 (accept_3_4 13 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 135 (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 135 (accept_3_4 10 92 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 135 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 92 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 135
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 135 (accept_3_4 7 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  135 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 135 (accept_3_4 4 92 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 92 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 135 (Polychromatic418967fa.accept_16_2_12_7_1_3410
  2 92 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 135 (accept_3_4 1 92
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92 135)))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  45 91 135 (Eq.refl Bool.true) (allA_succ_of_accept 44 91 135 (accept_3_5 44 91 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 91 135 (Polychromatic418967fa.accept_17_9_6_16_1_3280 43 91 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 135
  (Polychromatic418967fa.accept_18_6_1_9_1_5551 42 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 135 (accept_3_5 41 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 91 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 135 (accept_3_5 38 91 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 135 (Polychromatic418967fa.accept_16_5_11_7_1_5635 37 91 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 135
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 135 (accept_3_5 35 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 135 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 91 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 135 (accept_3_5 32 91 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 135 (Polychromatic418967fa.accept_16_15_11_7_1_6951 31 91 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 135
  (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 135 (accept_3_5 29 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 135 (Polychromatic418967fa.accept_17_10_6_16_1_6862 27 91 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 135 (accept_3_5 26 91 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 135 (Polychromatic418967fa.accept_19_6_15_2_1_2857 25 91
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 135
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 135 (accept_3_5 23 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 135 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 91 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 135 (accept_3_5 20 91 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 91 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 135
  (Polychromatic418967fa.accept_16_2_11_7_1_2352 18 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 135 (accept_3_5 17 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 135 (Polychromatic418967fa.accept_16_15_11_7_1_6951 15 91 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 135 (accept_3_5 14 91 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 135 (Polychromatic418967fa.accept_19_13_15_2_1_4126 13 91
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 135
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 135 (accept_3_5 11 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 91 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 135 (accept_3_5 8 91 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 135 (Polychromatic418967fa.accept_17_7_6_16_1_2195 7 91 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 135
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 135 (accept_3_5 5 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 135 (Polychromatic418967fa.accept_16_3_11_7_1_770 3 91 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 135 (accept_3_5 2 91 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 135 (Polychromatic418967fa.accept_19_1_15_2_1_6950 1 91 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 135))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46
  90 135 (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 135 45 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 90 135 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 90 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 90 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 135 3 14 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 90 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 135 5 8 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 90 135 3 13 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 90 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 90 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 135 9 4 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 90 135 5 7 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 90 135 (Polychromatic418967fa.accept_11_1_2_3_1_688 34 90 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 90 135 3 11 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 90 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 32
  90 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 135
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 90 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 135 15 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 90 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 135 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 90 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 90 135 9 3 10 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 90 135
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 90 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 90 135 5 5 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 90 135 3 8 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 90 135 (Polychromatic418967fa.accept_11_1_2_3_1_688 23 90 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 90 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 135 3 7 30 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 90 135 5 4 18 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 135
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 19 90 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 135 9 2 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 135 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 90 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 135 15 1 6 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 135
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 90 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 135 3 4 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 90 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 135 5 2 18 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 135 9 1 10 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 90 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 90 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 90 135 (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 90 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 135 3 2 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 135 5 1 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 90 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 90 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 135 3 1 30 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 135
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 90 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90 135)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 89 135
  (Eq.refl Bool.true) (allA_succ_of_accept 46 89 135 (accept_3_4 46 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 89 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 89 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 135 (accept_3_4 43 89 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 135
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 135 (accept_3_4 40 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 135 (accept_3_4 37 89 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 135 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 89 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 135
  (Polychromatic418967fa.accept_11_2_1_3_1_683 35 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 135 (accept_3_4 34 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 135 (accept_3_4 31 89 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 135
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 29 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 135 (accept_3_4 28 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 135 (Polychromatic418967fa.accept_19_8_13_2_1_6921 27 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 135 (accept_3_4 25 89 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 89 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 135
  (Polychromatic418967fa.accept_20_3_9_15_1_6847 23 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 135 (accept_3_4 22 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 135 (accept_3_4 19 89 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 135 (accept_3_4 16 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 135 (Polychromatic418967fa.accept_17_15_4_16_1_6890 15 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 135 (accept_3_4 13 89 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 135 (Polychromatic418967fa.accept_18_12_17_9_1_5513 12 89 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 135
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 135 (accept_3_4 10 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 135 (accept_3_4 7 89 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 135
  (Polychromatic418967fa.accept_17_5_4_16_1_6925 5 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 135 (accept_3_4 4 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  135 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 89 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 135 (accept_3_4 1 89 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 135))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 88 135 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 88 135 (accept_3_5 47 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 135 (Polychromatic418967fa.accept_25_21_13_10_1_6949 46 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 135 (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 88 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 135 (accept_3_5 44 88 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 135
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 135 (accept_3_5 41 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 135 (Polychromatic418967fa.accept_19_1_12_2_1_6918 39 88 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 135 (accept_3_5 38 88 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 135
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 36 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 135 (accept_3_5 35 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 88 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 135 (accept_3_5 32 88 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 135
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 135 (accept_3_5 29 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 135 (Polychromatic418967fa.accept_13_2_10_5_1_1643 28 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 88 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 135 (accept_3_5 26 88 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 135
  (Polychromatic418967fa.accept_17_7_3_16_1_2208 24 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 135 (accept_3_5 23 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 135 (Polychromatic418967fa.accept_13_8_10_5_1_977 21 88 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 135 (accept_3_5 20 88 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 135
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 135 (accept_3_5 17 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 135 (Polychromatic418967fa.accept_14_2_4_9_1_2121 16 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 135 (Polychromatic418967fa.accept_13_2_10_5_1_1643 15 88 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 135 (accept_3_5 14 88 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 135
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 135 (accept_3_5 11 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 135 (Polychromatic418967fa.accept_19_10_12_2_1_6948 10 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 135 (Polychromatic418967fa.accept_16_9_8_7_1_4529 9 88 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 135 (accept_3_5 8 88 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 135
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 135 (accept_3_5 5 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  135 (Polychromatic418967fa.accept_13_4_10_5_1_1644 4 88 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 88 135 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 88 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 135 (accept_3_5 2 88 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 135))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 87 135 (Eq.refl Bool.true) (allA_succ_of_gcd 48 87 135 3 16 29 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 135 (Polychromatic418967fa.accept_18_10_15_9_1_1054 46 87 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 135 3 15 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 135 (Polychromatic418967fa.accept_21_2_3_9_1_1317
  44 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 135 3 14 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 87 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 87 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 135 3 13 29 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 135
  (Polychromatic418967fa.accept_10_8_7_5_1_602 38 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 135 (Polychromatic418967fa.accept_21_16_3_9_1_6947 37 87 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 135 3 12 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 135 (Polychromatic418967fa.accept_17_1_2_16_1_5596
  35 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 135 3 11 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 135 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 87 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 135 (Polychromatic418967fa.accept_17_14_2_16_1_4380 31 87
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 135 3 10 29 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 135 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 87 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 135 3 9 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 87 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 135
  (Polychromatic418967fa.accept_17_8_2_16_1_5598 25 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 135 3 8 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 87 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 87 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 135 3 7 29 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 87 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 135 3 6 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 135 (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 87 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 135
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 16 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 135 3 5 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 135 (Polychromatic418967fa.accept_13_1_9_5_1_1598 14 87 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 87 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 135 3 4 29 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 135
  (Polychromatic418967fa.accept_18_11_15_9_1_360 11 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 135 (Polychromatic418967fa.accept_18_10_15_9_1_1054 10 87 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 135 3 3 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 87 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 135
  (Polychromatic418967fa.accept_11_7_10_3_1_633 7 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 135 3 2 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 87 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 135 (Polychromatic418967fa.accept_13_4_9_5_1_1641 4 87 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 135 3 1 29 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 135
  (Polychromatic418967fa.accept_10_2_7_5_1_605 2 87 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 87 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87 135))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 86
  135 (Eq.refl Bool.true) (allA_succ_of_accept 49 86 135 (accept_3_4 49 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 86 135 (Polychromatic418967fa.accept_21_6_2_9_1_5292 48 86 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 86 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 86 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 135 (accept_3_4 46 86 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 135
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 135 (accept_3_4 43 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 135 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 135 (accept_3_4 40 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 135 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 86 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 135
  (Polychromatic418967fa.accept_13_12_8_5_1_976 38 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 135 (accept_3_4 37 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 135 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 135 (accept_3_4 34 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 135
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 32 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 135 (accept_3_4 31 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 135 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 135 (accept_3_4 28 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 135 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 86 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 135
  (Polychromatic418967fa.accept_23_3_17_20_1_3494 26 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 135 (accept_3_4 25 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 135 (accept_3_4 22 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 135
  (Polychromatic418967fa.accept_21_20_2_9_1_5337 20 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 135 (accept_3_4 19 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 135 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 135 (accept_3_4 16 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 135 (Polychromatic418967fa.accept_16_15_6_7_1_4512 15 86 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 135
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 135 (accept_3_4 13 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 135 (Polychromatic418967fa.accept_13_12_8_5_1_976 12 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 135 (accept_3_4 10 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 135
  (Polychromatic418967fa.accept_19_8_10_2_1_5414 8 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 135 (accept_3_4 7 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  135 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 86 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 135 (accept_3_4 4 86 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 86 135 (Polychromatic418967fa.accept_13_3_8_5_1_974 3 86 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 135
  (Polychromatic418967fa.accept_17_2_1_16_1_6946 2 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 86 135 (accept_3_4 1 86 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  135)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 85 135 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  85 135 5 10 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  49 85 135 (Polychromatic418967fa.accept_11_5_8_3_1_66 49 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 85 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 85 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 135 (accept_3_5 47 85 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 85 135 5 9 17 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 135 (accept_3_5 44 85 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 135 (Polychromatic418967fa.accept_16_11_5_7_1_2395 43 85
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 135 (accept_3_5 41 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 85
  135 5 8 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  85 135 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 85 135 (accept_3_5 38 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 85 135 (Polychromatic418967fa.accept_13_11_7_5_1_2314 37 85 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 135 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 85 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 85 135 5 7 17 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 85 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 85 135 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 85 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 135 (accept_3_5 32 85 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 85 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 85 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 85 135 5 6 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 85 135 (accept_3_5 29 85 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 135 (accept_3_5 26 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85
  135 5 5 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  85 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 85 135 (accept_3_5 23 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 85 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 135 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 85 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 85 135 5 4 17 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 85 135
  (Polychromatic418967fa.accept_20_19_5_15_1_5380 19 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 85 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 135 (accept_3_5 17 85 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 85 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 135 5 3 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 135 (accept_3_5 14 85 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 85 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 135
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 135 (accept_3_5 11 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85
  135 5 2 17 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  85 135 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 85 135 (accept_3_5 8 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 85 135 (Polychromatic418967fa.accept_19_7_9_2_1_4090 7 85 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 85 135 5 1 17 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 85 135
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 85 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 135 (accept_3_5 2 85 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 135 (Polychromatic418967fa.accept_19_1_9_2_1_6945 1 85 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 135)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 84 135 (Eq.refl Bool.true) (allA_succ_of_gcd 51 84 135 3 17 28 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 135
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 50 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 84 135 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 84 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 135 3 16 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 135 (Polychromatic418967fa.accept_18_11_12_9_1_992
  47 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 135
  (Polychromatic418967fa.accept_10_6_4_5_1_615 46 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 84 135 3 15 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 84 135 (Polychromatic418967fa.accept_16_12_4_7_1_3391 44 84 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 84 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 135 3 14 28 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 135
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 135 (Polychromatic418967fa.accept_13_1_6_5_1_1610 40 84 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 84 135 3 13 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 84 135 (Polychromatic418967fa.accept_13_12_6_5_1_2335
  38 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 135
  (Polychromatic418967fa.accept_11_4_7_3_1_289 37 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 135 3 12 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 84 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 135 (Polychromatic418967fa.accept_18_16_12_9_1_5504 34 84
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 135 3 11 28 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 135
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 32 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 84 135 (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 84 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 135 3 10 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 135 (Polychromatic418967fa.accept_10_9_4_5_1_616 29
  84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 135
  (Polychromatic418967fa.accept_16_12_4_7_1_3391 28 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 84 135 3 9 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 84 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 84 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 135 (Polychromatic418967fa.accept_13_12_6_5_1_2335 25 84
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 135 3 8 28 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 135
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 135 (Polychromatic418967fa.accept_18_4_12_9_1_2011 22 84 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 135 3 7 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 135 (Polychromatic418967fa.accept_19_1_8_2_1_2876 20 84 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 135
  (Polychromatic418967fa.accept_8_3_4_7_1_475 19 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 135 3 6 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 135 (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 84 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 84 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 135 3 5 28 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 84 135
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 84 135 (Polychromatic418967fa.accept_16_13_4_7_1_1537 13 84 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 135 3 4 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 84 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 135
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 84 135 3 3 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 84 135 (Polychromatic418967fa.accept_16_8_4_7_1_3390 8 84 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 135 (Polychromatic418967fa.accept_22_7_18_3_1_6905 7 84 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 135 3 2 28 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 135
  (Polychromatic418967fa.accept_18_5_12_9_1_6871 5 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 135 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 84 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 135 3 1 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 135 (Polychromatic418967fa.accept_20_2_4_15_1_6911 2 84 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 135
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 84 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 135)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 83 135 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 83 135 (accept_3_4 52 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 135 (Polychromatic418967fa.accept_18_15_11_9_1_4256 51 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 135 (accept_3_4 49 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 135 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 83 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 135
  (Polychromatic418967fa.accept_10_7_3_5_1_301 47 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 135 (accept_3_4 46 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 135 (accept_3_4 43 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 135 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 83 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 135
  (Polychromatic418967fa.accept_11_8_6_3_1_661 41 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 135 (accept_3_4 40 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 135 (accept_3_4 37 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 83 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 135
  (Polychromatic418967fa.accept_17_1_15_16_1_2202 35 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 135 (accept_3_4 34 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 135 (accept_3_4 31 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 135 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 83 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 135 (accept_3_4 28 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 135 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 135 (accept_3_4 25 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 83 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 135
  (Polychromatic418967fa.accept_19_4_7_2_1_6944 23 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 135 (accept_3_4 22 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 135 (accept_3_4 19 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 83 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 135
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 135 (accept_3_4 16 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 135 (accept_3_4 13 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 135 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 83 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 135
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 135 (accept_3_4 10 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 135 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 135 (accept_3_4 7 83 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 135 (Polychromatic418967fa.accept_21_6_20_9_1_6943 6 83 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 135
  (Polychromatic418967fa.accept_19_5_7_2_1_1728 5 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 135 (accept_3_4 4 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  135 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 83 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 83 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 135 (accept_3_4 1 83 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 135))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 82 135 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 82 135 (accept_3_5 53 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 82 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 82 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 135 (Polychromatic418967fa.accept_13_12_4_5_1_1637 51 82
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 135 (accept_3_5 50 82 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 135
  (Polychromatic418967fa.accept_10_8_2_5_1_596 48 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 135 (accept_3_5 47 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 135 (accept_3_5 44 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 82 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 135
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 135 (accept_3_5 41 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 135 (Polychromatic418967fa.accept_13_1_4_5_1_113 40 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 135 (accept_3_5 38 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 135
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 135 (accept_3_5 35 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 135 (Polychromatic418967fa.accept_19_15_6_2_1_6865 34 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 135 (accept_3_5 32 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 82 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 135
  (Polychromatic418967fa.accept_11_8_5_3_1_694 30 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 135 (accept_3_5 29 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 135 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 135 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 135 (accept_3_5 26 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 135 (accept_3_5 23 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 135 (Polychromatic418967fa.accept_13_9_4_5_1_1651 22 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 135 (accept_3_5 20 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 82 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 135
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 135 (accept_3_5 17 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 135 (Polychromatic418967fa.accept_23_16_13_20_1_6942 16 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 135 (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 135 (accept_3_5 14 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 135
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 135 (accept_3_5 11 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 135 (accept_3_5 8 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 82 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 135
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 135 (accept_3_5 5 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  135 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 82 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 82 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 135 (accept_3_5 2 82 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 135))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 81 135 (Eq.refl Bool.true) (allA_succ_of_gcd 54 81 135 27 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 81 135 (Polychromatic418967fa.accept_12_5_9_3_1_85 53
  81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 135
  (Polychromatic418967fa.accept_19_14_5_2_1_6941 52 81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 81 135 3 17 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 81 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 81 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 135 3 16 27 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 135
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 81 135 9 5 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 81 135 (Polychromatic418967fa.accept_10_4_1_5_1_1018 44 81 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 135
  (Polychromatic418967fa.accept_12_7_9_3_1_767 43 81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 81 135 3 14 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 81 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 81 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 81 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 135 3 13 27 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 135 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 81 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 81 135 9 4 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 81 135 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 81 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 81 135 3 11 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 81 135 (Polychromatic418967fa.accept_13_6_3_5_1_3167 32 81 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 135 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 81 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 135 3 10 27 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 135
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 135 (Polychromatic418967fa.accept_13_2_3_5_1_2294 28 81 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 135 27 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 135
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 81 135 3 8 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 81 135 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 81 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 135 3 7 27 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 135
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 81 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 135 9 2 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 135 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 81 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 135
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 81 135 3 5 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 81 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 81 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 135 3 4 27 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 135
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 135 9 1 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 135 (Polychromatic418967fa.accept_13_8_3_5_1_1636 8 81 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 135
  (Polychromatic418967fa.accept_11_7_4_3_1_302 7 81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 81 135 3 2 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 81 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 81 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 135 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 81 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 135 3 1 27 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 135 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 81 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 81 135))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56
  80 135 (Eq.refl Bool.true) (allA_succ_of_gcd 55 80 135 5 11 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 80 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 80 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 80 135
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 80 135 (accept_3_4 52 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  80 135 (Polychromatic418967fa.accept_13_12_2_5_1_1634 51 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 80 135 5 10 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 80 135 (accept_3_4 49 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 80 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 80 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 80 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 135 (accept_3_4 46 80 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 80 135 5 9 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 80 135 (Polychromatic418967fa.accept_19_6_4_2_1_1726
  44 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 80 135 (accept_3_4 43
  80 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 80 135
  (Polychromatic418967fa.accept_12_6_8_3_1_82 42 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 80 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 135 5 8 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 135 (Polychromatic418967fa.accept_18_3_8_9_1_1956 39 80 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 135
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 38 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 135 (accept_3_4 37 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 80 135 5 7 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 80 135 (accept_3_4 34 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 80 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 80 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 135 (Polychromatic418967fa.accept_23_9_11_20_1_6940 32 80
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 80 135 (accept_3_4 31 80 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 135 5 6 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 29
  80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 135 (accept_3_4 28 80
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 80 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 80 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 80 135 5 5 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 80 135 (Polychromatic418967fa.accept_18_6_8_9_1_1960 24 80 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 135
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 80 135 (accept_3_4 22 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  80 135 (Polychromatic418967fa.accept_18_3_8_9_1_1956 21 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 80 135 5 4 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 80 135 (accept_3_4 19 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 80 135 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 80 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 80 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 135 (accept_3_4 16 80 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 80 135 5 3 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 80 135 (Polychromatic418967fa.accept_19_14_4_2_1_2840
  14 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 135 (accept_3_4 13
  80 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 80 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 80 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 135 5 2 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 135 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 80 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 135 (accept_3_4 7 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  135 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 80 135 5 1 16 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 80 135 (accept_3_4 4 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80
  135 (Polychromatic418967fa.accept_13_3_2_5_1_1632 3 80 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 80 135 (Polychromatic418967fa.accept_21_2_17_9_1_6895 2 80 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 135 (accept_3_4 1 80 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 80 135)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 79 135
  (Eq.refl Bool.true) (allA_succ_of_accept 56 79 135 (accept_3_5 56 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 79 135 (Polychromatic418967fa.accept_13_3_1_5_1_499 55 79 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 135 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 79 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 135 (accept_3_5 53 79 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 52
  79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 135
  (Polychromatic418967fa.accept_10_1_9_5_1_83 51 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 135 (accept_3_5 50 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 135 (Polychromatic418967fa.accept_17_15_11_16_1_3263 49 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 135 (Polychromatic418967fa.accept_13_9_1_5_1_964 48 79 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 135 (accept_3_5 47 79 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 79 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 135
  (Polychromatic418967fa.accept_11_1_2_3_1_688 45 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 135 (accept_3_5 44 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 135 (Polychromatic418967fa.accept_13_4_1_5_1_1628 43 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 135 (Polychromatic418967fa.accept_13_3_1_5_1_499 42 79 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 135 (accept_3_5 41 79 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 135
  (Polychromatic418967fa.accept_17_5_11_16_1_3257 39 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 135 (accept_3_5 38 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 135 (Polychromatic418967fa.accept_19_18_3_2_1_6939 37 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 135 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 79 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 135 (accept_3_5 35 79 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 79 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 135
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 135 (accept_3_5 32 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 135 (Polychromatic418967fa.accept_13_4_1_5_1_1628 30 79 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 135 (accept_3_5 29 79 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 135
  (Polychromatic418967fa.accept_16_11_15_7_1_5654 27 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 135 (accept_3_5 26 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 135 (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 135 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 79 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 135 (accept_3_5 23 79 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 79 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 135
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 135 (accept_3_5 20 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 135 (Polychromatic418967fa.accept_13_6_1_5_1_3988 19 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 135 (Polychromatic418967fa.accept_19_18_3_2_1_6939 18 79 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 135 (accept_3_5 17 79 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 135
  (Polychromatic418967fa.accept_17_15_11_16_1_3263 15 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 79 135 (accept_3_5 14 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 79 135 (Polychromatic418967fa.accept_21_13_16_9_1_2541 13 79 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 135 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 79 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 135 (accept_3_5 11 79 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 10
  79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 135
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 135 (accept_3_5 8 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  135 (Polychromatic418967fa.accept_21_7_16_9_1_2417 7 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 135 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 79 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 135 (accept_3_5 5 79 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 135
  (Polychromatic418967fa.accept_13_3_1_5_1_499 3 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 135 (accept_3_5 2 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  135 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 79 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 135))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 78 135 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 78 135 3 19 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 78 135 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 78 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 135 3 18 26 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 78 135 3 17 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 78 135 (Polychromatic418967fa.accept_12_2_6_3_1_331 50
  78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 135 3 16 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 78 135 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 135 (Polychromatic418967fa.accept_11_2_1_3_1_683 46 78 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 135 3 15 26 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 135
  (Polychromatic418967fa.accept_12_8_6_3_1_366 44 78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 78 135 (Polychromatic418967fa.accept_10_3_8_5_1_606 43 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 135 3 14 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 135
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 78 135 3 13 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 78 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 135 3 12 26 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 135
  (Polychromatic418967fa.accept_11_2_1_3_1_683 35 78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 78 135 3 11 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 78 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 32
  78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 135
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 135 3 10 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 135 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 78 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 135 3 9 26 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 135
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 78 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 135 3 8 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 135 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 78 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 135
  (Polychromatic418967fa.accept_10_2_8_5_1_587 22 78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 78 135 3 7 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 78 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 135 (Polychromatic418967fa.accept_18_1_6_9_1_2001 19 78 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 135 3 6 26 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 135 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 78 135 3 5 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 78 135 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 78 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 135 3 4 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 135 (Polychromatic418967fa.accept_21_11_15_9_1_3868 11 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 78 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 135 3 3 26 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 135
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 78 135 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 135 3 2 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 135
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 78 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 78 135 3 1 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 78 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 78 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  135)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 77 135 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 77 135 (accept_3_4 58 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 135 (accept_3_4 55 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 135
  (Polychromatic418967fa.accept_10_3_7_5_1_288 53 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 135 (accept_3_4 52 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 135 (Polychromatic418967fa.accept_18_15_5_9_1_5529 51 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 135 (accept_3_4 49 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 135 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 77 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 135
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 47 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 135 (accept_3_4 46 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 135 (accept_3_4 43 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 135
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 135 (accept_3_4 40 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 135 (Polychromatic418967fa.accept_20_19_17_15_1_2690 39 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 135 (accept_3_4 37 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 135 (Polychromatic418967fa.accept_16_4_13_7_1_4522 36 77 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 135
  (Polychromatic418967fa.accept_22_13_11_3_1_6889 35 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 135 (accept_3_4 34 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 135 (accept_3_4 31 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 135
  (Polychromatic418967fa.accept_36_29_5_27_1_4245 29 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 135 (accept_3_4 28 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 135 (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 135 (accept_3_4 25 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 135 (Polychromatic418967fa.accept_21_3_14_9_1_5299 24 77 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 135
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 135 (accept_3_4 22 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 135 (accept_3_4 19 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 135
  (Polychromatic418967fa.accept_13_4_12_5_1_476 17 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 135 (accept_3_4 16 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 135 (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 135 (accept_3_4 13 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 135 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 77 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 135
  (Polychromatic418967fa.accept_23_11_8_20_1_6938 11 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 135 (accept_3_4 10 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 135 (accept_3_4 7 77 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 135
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 5 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 135 (accept_3_4 4 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  135 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 77 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 135 (accept_3_4 1 77 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 135))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 76 135 (Eq.refl
  Bool.true) (allA_succ_of_accept 59 76 135 (accept_3_5 59 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 76 135 (Polychromatic418967fa.accept_13_6_11_5_1_133 58 76 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 76 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 135 (accept_3_5 56 76 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 55
  76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 135
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 135 (accept_3_5 53 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 135 (accept_3_5 50 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 135
  (Polychromatic418967fa.accept_17_14_8_16_1_6863 48 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 135 (accept_3_5 47 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 135 (accept_3_5 44 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 135
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 135 (accept_3_5 41 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 135 (Polychromatic418967fa.accept_11_7_10_3_1_633 40 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 135 (accept_3_5 38 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 135 (accept_3_5 35 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 135 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 76 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 135 (accept_3_5 32 76 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 135
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 135 (accept_3_5 29 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 135 (Polychromatic418967fa.accept_21_7_13_9_1_6937 28 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 135 (accept_3_5 26 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 135
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 135 (accept_3_5 23 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 135 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 135 (accept_3_5 20 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 135
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 135 (accept_3_5 17 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 135 (Polychromatic418967fa.accept_13_3_11_5_1_2348 16 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 135 (accept_3_5 14 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 135
  (Polychromatic418967fa.accept_18_12_4_9_1_5452 12 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 135 (accept_3_5 11 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 135 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 135 (accept_3_5 8 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 135
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 135 (accept_3_5 5 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  135 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 76 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 76 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 76 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 135 (accept_3_5 2 76 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 76 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 135))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 75 135 (Eq.refl Bool.true) (allA_succ_of_gcd 60 75 135 15 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 59
  75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 135
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 58 75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 135 3 19 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 135 (Polychromatic418967fa.accept_13_4_10_5_1_1644 56 75 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 135 5 11 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 75 135 3 18 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 53
  75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 52 75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 75 135 3 17 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 75 135 5 10 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 75 135 (Polychromatic418967fa.accept_14_7_5_9_1_2911 49 75 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 75 135 3 16 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 135 (Polychromatic418967fa.accept_13_8_10_5_1_977
  47 75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 135
  (Polychromatic418967fa.accept_7_4_5_2_1_243 46 75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 75 135 15 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 75 135 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 75 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 135 (Polychromatic418967fa.accept_13_4_10_5_1_1644 43 75
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 135 3 14 25 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 135
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 41 75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 75 135 5 8 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 75 135 3 13 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 75 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 135 (Polychromatic418967fa.accept_16_5_11_7_1_5635 37 75
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 135 3 12 25 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 75 135 5 7 15 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 75 135
  (Polychromatic418967fa.accept_13_8_10_5_1_977 34 75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 75 135 3 11 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 75 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 75 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 75 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 135 15 2 5 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 135
  (Polychromatic418967fa.accept_19_10_18_2_1_6936 29 75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 135 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 75 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 135 3 9 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 135 (Polychromatic418967fa.accept_18_8_3_9_1_4232 26 75 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 75 135 5 5 15 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 75 135 3 8 25 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 135
  (Polychromatic418967fa.accept_17_6_7_16_1_6836 23 75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 135 (Polychromatic418967fa.accept_19_3_18_2_1_6935 22 75 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 135 3 7 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 75 135 5 4 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 135 (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 75 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 135 3 6 25 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 135 (Polychromatic418967fa.accept_19_16_18_2_1_6934 16 75 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 135 15 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 135 (Polychromatic418967fa.accept_18_14_3_9_1_4234 14 75 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 135
  (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 135 3 4 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 75 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 135 5 2 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 75 135 3 3 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 135 (Polychromatic418967fa.accept_13_8_10_5_1_977 8 75 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 135
  (Polychromatic418967fa.accept_14_7_5_9_1_2911 7 75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 75 135 3 2 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 75 135 5 1 15 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 75 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 75 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 135 3 1 25 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 135 (Polychromatic418967fa.accept_13_2_10_5_1_1643 2 75 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 135
  (Polychromatic418967fa.accept_18_1_3_9_1_328 1 75 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 135))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 74 135 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 74 135 (accept_3_4 61 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 74 135 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 74 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 74 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 74 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 135 (accept_3_4 58 74 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 135
  (Polychromatic418967fa.accept_10_6_4_5_1_615 56 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 135 (accept_3_4 55 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 135 (accept_3_4 52 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 135 (Polychromatic418967fa.accept_10_1_4_5_1_1031 51 74 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 135
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 50 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 135 (accept_3_4 49 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 135 (accept_3_4 46 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 135
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 44 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 135 (accept_3_4 43 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 135 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 135 (accept_3_4 40 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 135 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 74 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 135
  (Polychromatic418967fa.accept_11_5_8_3_1_66 38 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 135 (accept_3_4 37 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 135 (accept_3_4 34 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 135
  (Polychromatic418967fa.accept_24_8_2_15_1_6933 32 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 135 (accept_3_4 31 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 135 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 135 (accept_3_4 28 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 74 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 135
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 135 (accept_3_4 25 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 135 (Polychromatic418967fa.accept_17_7_6_16_1_2195 24 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 135 (accept_3_4 22 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 135
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 135 (accept_3_4 19 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 135 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 135 (accept_3_4 16 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 135 (Polychromatic418967fa.accept_13_2_9_5_1_959 15 74 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 135
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 14 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 135 (accept_3_4 13 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 135 (accept_3_4 10 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 135
  (Polychromatic418967fa.accept_20_8_14_15_1_6932 8 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 135 (accept_3_4 7 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  135 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 135 (accept_3_4 4 74 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 135 (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 74 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 135 (Polychromatic418967fa.accept_13_2_9_5_1_959 2
  74 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 135 (accept_3_4 1 74 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  135)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 73 135 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 73 135 (accept_3_5 62 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  73 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 73 135 (Polychromatic418967fa.accept_18_6_1_9_1_5551 60 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 73 135 (accept_3_5 59 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 73 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 73 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 73 135 (accept_3_5 56 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  73 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 73 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 135 (accept_3_5 53 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 73 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 135
  (Polychromatic418967fa.accept_13_12_8_5_1_976 51 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 73 135 (accept_3_5 50 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  73 135 (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 73 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 135 (accept_3_5 47 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 73 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 135
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 73 135 (accept_3_5 44 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  73 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 73 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 135 (accept_3_5 41 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 135
  (Polychromatic418967fa.accept_18_3_1_9_1_1929 39 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 73 135 (accept_3_5 38 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  73 135 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 73 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 135 (accept_3_5 35 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 73 135 (accept_3_5 32 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 135 (Polychromatic418967fa.accept_20_11_13_15_1_6931 31 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 135 (accept_3_5 29 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 135 (accept_3_5 26 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 135 (Polychromatic418967fa.accept_13_12_8_5_1_976 25 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 135 (Polychromatic418967fa.accept_16_8_9_7_1_768 24 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 135 (accept_3_5 23 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 135
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 135 (accept_3_5 20 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 135 (accept_3_5 17 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 135 (accept_3_5 14 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 135 (accept_3_5 11 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 135
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 135 (accept_3_5 8 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  135 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 135 (accept_3_5 5 73 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 135 (Polychromatic418967fa.accept_13_3_8_5_1_974 3
  73 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 135 (accept_3_5 2 73 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 73
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  135))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 72 135 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 72 135 9 7 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 135 (Polychromatic418967fa.accept_22_18_6_3_1_6929 62 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 135 (Polychromatic418967fa.accept_23_15_3_20_1_6930 61 72
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 135 3 20 24 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 135
  (Polychromatic418967fa.accept_25_9_22_10_1_6928 59 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 135 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 135 3 19 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 135 (Polychromatic418967fa.accept_17_5_4_16_1_6925
  56 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 135
  (Polychromatic418967fa.accept_19_17_15_2_1_6887 55 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 135 9 6 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 135 (Polychromatic418967fa.accept_10_3_2_5_1_295 53 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 135 (Polychromatic418967fa.accept_11_8_6_3_1_661 52 72 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 135 3 17 24 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 135
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 50 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 135 (Polychromatic418967fa.accept_14_7_2_9_1_2093 49 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 135 3 16 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 135 (Polychromatic418967fa.accept_10_7_2_5_1_298 47
  72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 135
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 46 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 135 9 5 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 135 (Polychromatic418967fa.accept_16_12_8_7_1_4530 44 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 135 (Polychromatic418967fa.accept_10_3_2_5_1_295 43 72 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 135 3 14 24 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 135
  (Polychromatic418967fa.accept_11_8_6_3_1_661 41 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 135 (Polychromatic418967fa.accept_22_18_6_3_1_6929 40 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 135 3 13 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 135 (Polychromatic418967fa.accept_10_8_2_5_1_596 38
  72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 135
  (Polychromatic418967fa.accept_10_7_2_5_1_298 37 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 135 9 4 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 135 (Polychromatic418967fa.accept_14_7_2_9_1_2093 35 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 135 (Polychromatic418967fa.accept_25_9_22_10_1_6928 34 72
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 135 3 11 24 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 135
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 32 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 135 (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 135 3 10 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 135 (Polychromatic418967fa.accept_22_7_6_3_1_3779
  29 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 135
  (Polychromatic418967fa.accept_10_8_2_5_1_596 28 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 135 9 3 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 135 (Polychromatic418967fa.accept_20_6_12_15_1_3938 26 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 135 (Polychromatic418967fa.accept_13_12_7_5_1_3147 25 72
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 135 3 8 24 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 135
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 135 (Polychromatic418967fa.accept_17_5_4_16_1_6925 22 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 135 3 7 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 135 (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 72 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 135
  (Polychromatic418967fa.accept_11_8_6_3_1_661 19 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 135 9 2 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 135 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 135 (Polychromatic418967fa.accept_25_16_22_10_1_6927 16 72
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 135 3 5 24 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 135
  (Polychromatic418967fa.accept_22_14_6_3_1_6926 14 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 135 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 135 3 4 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 135 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 72 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 135
  (Polychromatic418967fa.accept_20_10_12_15_1_3940 10 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 72 135 9 1 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 72 135 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 72 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 135 (Polychromatic418967fa.accept_10_7_2_5_1_298 7
  72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 135 3 2 24 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 135
  (Polychromatic418967fa.accept_17_5_4_16_1_6925 5 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 135 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 72 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 135 3 1 24 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 135 (Polychromatic418967fa.accept_13_2_7_5_1_3189 2 72 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 135
  (Polychromatic418967fa.accept_16_1_8_7_1_3377 1 72 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 135)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 71 135 (Eq.refl
  Bool.true) (allA_succ_of_accept 64 71 135 (accept_3_4 64 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 71 135 (Polychromatic418967fa.accept_11_8_5_3_1_694 63 71 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 71 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 71 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 135 (accept_3_4 61 71 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 135 (Polychromatic418967fa.accept_21_18_8_9_1_2457
  60 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 135
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 135 (accept_3_4 58 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 135 (accept_3_4 55 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 135 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 71 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 135
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 53 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 135 (accept_3_4 52 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 135 (Polychromatic418967fa.accept_13_12_6_5_1_2335 51 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 135 (accept_3_4 49 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 71 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 135
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 47 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 135 (accept_3_4 46 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 135 (accept_3_4 43 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 135 (Polychromatic418967fa.accept_13_3_6_5_1_2336 42 71 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 135 (accept_3_4 40 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 135 (accept_3_4 37 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 135 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 71 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 135
  (Polychromatic418967fa.accept_19_16_14_2_1_6924 35 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 135 (accept_3_4 34 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 135 (accept_3_4 31 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 135 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 71 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 135
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 135 (accept_3_4 28 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 135 (accept_3_4 25 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 71 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 135
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 135 (accept_3_4 22 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 135 (accept_3_4 19 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 135 (Polychromatic418967fa.accept_21_18_8_9_1_2457 18 71 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 135
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 135 (accept_3_4 16 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 135 (Polychromatic418967fa.accept_18_15_17_9_1_4200 15 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 135 (accept_3_4 13 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 135 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 71 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 135
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 135 (accept_3_4 10 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 135 (accept_3_4 7 71 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 71 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 135
  (Polychromatic418967fa.accept_19_5_14_2_1_1716 5 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 135 (accept_3_4 4 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  135 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 71 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 71 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 135 (accept_3_4 1 71 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 135))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 70 135
  (Eq.refl Bool.true) (allA_succ_of_gcd 65 70 135 5 13 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 70 135 (Polychromatic418967fa.accept_19_7_13_2_1_2878 64 70 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 135
  (Polychromatic418967fa.accept_16_15_6_7_1_4512 63 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 135 (accept_3_5 62 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 70 135 5 12 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 70 135 (accept_3_5 59 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 70 135 (Polychromatic418967fa.accept_19_1_13_2_1_6923 58 70 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 70 135 (accept_3_5 56 70 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 70 135 5 11 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 70 135
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 70 135 (accept_3_5 53 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  70 135 (Polychromatic418967fa.accept_17_1_2_16_1_5596 52 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 70 135 (Polychromatic418967fa.accept_11_7_4_3_1_302 51 70 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 135 5 10 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 70 135 (Polychromatic418967fa.accept_17_14_2_16_1_4380 48 70 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 135 (accept_3_5 47 70 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 70 135 (Polychromatic418967fa.accept_19_8_13_2_1_6921 46 70 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 70 135 5 9 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 70 135 (accept_3_5 44 70 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 70 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 135
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 70 135 (accept_3_5 41 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  135 5 8 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 135 (Polychromatic418967fa.accept_17_5_2_16_1_1294 39 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 70 135 (accept_3_5 38 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 70 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 135 (Polychromatic418967fa.accept_20_16_10_15_1_5368 36 70
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 70 135 5 7 14 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 70 135
  (Polychromatic418967fa.accept_19_15_13_2_1_6851 34 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 70 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 135 (accept_3_5 32 70 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 70 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 70 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 135 5 6 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 135 (accept_3_5 29 70 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 135 (Polychromatic418967fa.accept_20_8_10_15_1_6922 28 70 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 135
  (Polychromatic418967fa.accept_19_8_13_2_1_6921 27 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 135 (accept_3_5 26 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 70
  135 5 5 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  70 135 (Polychromatic418967fa.accept_20_4_10_15_1_6919 24 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 70 135 (accept_3_5 23 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 70 135 (Polychromatic418967fa.accept_17_5_2_16_1_1294 22 70 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 135 5 4 14 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 135
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 70 135 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 70 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 135 (accept_3_5 17 70 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 70 135 (Polychromatic418967fa.accept_19_16_13_2_1_6920 16 70 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 70 135 5 3 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 70 135 (accept_3_5 14 70 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 135
  (Polychromatic418967fa.accept_18_12_16_9_1_4198 12 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 135 (accept_3_5 11 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  135 5 2 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 135 (accept_3_5 8 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 135 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 70 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 70 135 5 1 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 70 135 (Polychromatic418967fa.accept_20_4_10_15_1_6919 4 70 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 135
  (Polychromatic418967fa.accept_20_3_10_15_1_620 3 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 135 (accept_3_5 2 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 135)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 69 135 (Eq.refl
  Bool.true) (allA_succ_of_gcd 66 69 135 3 22 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 69 135 (Polychromatic418967fa.accept_12_5_9_3_1_85 65 69 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 64
  69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 135 3 21 23 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 61 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 69 135 3 20 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 69 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 59
  69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 69 135 3 19 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 69 135 (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 135 (Polychromatic418967fa.accept_12_7_9_3_1_767 55 69 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 135 3 18 23 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 135
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 69 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 69 135 3 17 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 69 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 135
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 69 135 3 16 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 69 135 (Polychromatic418967fa.accept_12_11_9_3_1_792 47 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 135 3 15 23 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 135
  (Polychromatic418967fa.accept_10_4_9_5_1_84 44 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 135 3 14 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 41
  69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 135
  (Polychromatic418967fa.accept_13_1_4_5_1_113 40 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 69 135 3 13 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 69 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 135 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 69 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 135 3 12 23 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 135
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 135 3 11 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 32
  69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 135
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 69 135 3 10 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 69 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 135 (Polychromatic418967fa.accept_13_2_4_5_1_3152 28 69 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 135 3 9 23 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 135 3 8 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 135 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 69 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 69 135 3 7 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 69 135 (Polychromatic418967fa.accept_19_1_12_2_1_6918 20 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 135 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 69 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 135 3 6 23 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 135
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 135 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 135 3 5 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 135
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 69 135 3 4 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 69 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 135 3 3 23 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 135 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 135 3 2 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 135 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 69 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 135
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 69 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 69 135 3 1 23 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 69 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 69 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  135))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 135 (allA_succ_of_accept 67 68
  135 (accept_3_4 67 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 66 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 135 (accept_3_4 64 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 135 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 135 (Polychromatic418967fa.accept_10_2_8_5_1_587
  62 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 135 (accept_3_4 61
  68 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 135
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 135 (accept_3_4 58 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 135 (Polychromatic418967fa.accept_10_7_8_5_1_1008 57 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 135 (Polychromatic418967fa.accept_11_1_2_3_1_688
  56 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 135 (accept_3_4 55
  68 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 135
  (Polychromatic418967fa.accept_12_6_8_3_1_82 54 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 135 (accept_3_4 52 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 135 (Polychromatic418967fa.accept_13_11_3_5_1_982
  50 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 135 (accept_3_4 49
  68 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 135
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 48 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 68 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 135 (accept_3_4 46 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 68 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 135 (Polychromatic418967fa.accept_16_12_4_7_1_3391
  44 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 135 (accept_3_4 43
  68 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 135
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 135 (accept_3_4 40 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 38
  68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 135 (accept_3_4 37 68
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 135
  (Polychromatic418967fa.accept_21_15_5_9_1_5315 36 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 135 (accept_3_4 34 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 135 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 135 (accept_3_4 31 68
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 135
  (Polychromatic418967fa.accept_12_6_8_3_1_82 30 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 68 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 135 (accept_3_4 28 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 68 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 135
  (Polychromatic418967fa.accept_23_3_22_20_1_6917 26 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 135 (accept_3_4 25 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 135 (accept_3_4 22 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 135 (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 68 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 135
  (Polychromatic418967fa.accept_22_20_2_3_1_6916 20 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 135 (accept_3_4 19 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 135 (accept_3_4 16 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 135 (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 68 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 135
  (Polychromatic418967fa.accept_13_1_3_5_1_140 14 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 135 (accept_3_4 13 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 135 (accept_3_4 10 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 135 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 68 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 135
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 8 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 135 (accept_3_4 7 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  135 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 135 (accept_3_4 4 68 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 68 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  68 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 135 (accept_3_4 1 68 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  135)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 135 (allA_succ_of_accept 66 67
  135 (Polychromatic418967fa.accept_30_6_7_15_1_6915 66 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 67 135 (accept_3_5 65 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 67 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 67 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 67 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 135 (accept_3_5 62 67 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 61
  67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 135
  (Polychromatic418967fa.accept_8_4_3_7_1_491 60 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 135 (accept_3_5 59 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 135 (Polychromatic418967fa.accept_11_2_1_3_1_683 57 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 135 (accept_3_5 56 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 67 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 135
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 135 (accept_3_5 53 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 135 (Polychromatic418967fa.accept_13_12_2_5_1_1634 51 67 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 135 (accept_3_5 50 67 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 135 (Polychromatic418967fa.accept_13_10_2_5_1_1633 49 67
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 135
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 135 (accept_3_5 47 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 135 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 135 (accept_3_5 44 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 67 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 135
  (Polychromatic418967fa.accept_10_2_7_5_1_605 42 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 135 (accept_3_5 41 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 135 (Polychromatic418967fa.accept_18_3_13_9_1_4260 39 67 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 135 (accept_3_5 38 67 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 135 (Polychromatic418967fa.accept_19_18_10_2_1_2850 37 67
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 135
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 135 (accept_3_5 35 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 135 (accept_3_5 32 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 135 (Polychromatic418967fa.accept_16_15_3_7_1_3389 31 67 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 135
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 135 (accept_3_5 29 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 135 (accept_3_5 26 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 135 (Polychromatic418967fa.accept_13_12_2_5_1_1634 25 67 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 135
  (Polychromatic418967fa.accept_11_2_1_3_1_683 24 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 135 (accept_3_5 23 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 135 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 135 (accept_3_5 20 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 67 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 135
  (Polychromatic418967fa.accept_10_8_7_5_1_602 18 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 135 (accept_3_5 17 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 135 (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 67 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 135 (accept_3_5 14 67 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 67 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 135
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 135 (accept_3_5 11 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 135 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 135 (accept_3_5 8 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 135 (Polychromatic418967fa.accept_13_7_2_5_1_2344 7 67 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 135
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 135 (accept_3_5 5 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 67 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 135 (accept_3_5 2 67 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 135 (Polychromatic418967fa.accept_20_1_7_15_1_1521 1 67 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  135))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 135 (allA_succ_of_accept 65 66
  135 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 135 3 21 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 62
  66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 135 3 20 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 135 (Polychromatic418967fa.accept_10_9_6_5_1_1002 59 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 135 (Polychromatic418967fa.accept_12_10_6_3_1_786 58 66 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 66 135 3 19 22 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 135
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 66 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 135 3 18 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 135
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 66 135 3 17 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 66 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 135 3 16 22 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 135 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 135 3 15 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 44
  66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 135 3 14 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 66 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 66 135 3 13 22 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 135
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 135 3 12 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 135 (Polychromatic418967fa.accept_13_9_1_5_1_964 35
  66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 66 135 3 11 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 66 135 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 135 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 66 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 135 3 10 22 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 135 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 135 3 9 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 66 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 135 3 8 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 135 (Polychromatic418967fa.accept_18_5_12_9_1_6871 23 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 66 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 135 3 7 22 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 135 3 6 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 135
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 135 3 5 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 135 3 4 22 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 135
  (Polychromatic418967fa.accept_10_1_6_5_1_304 11 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 135 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 135 3 3 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 66 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 135
  (Polychromatic418967fa.accept_19_7_9_2_1_4090 7 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 135 3 2 22 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 66 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 135 3 1 22 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 135
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 66 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 135))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 135 (allA_succ_of_accept 64 65 135 (accept_3_4 64 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 65 135 (Polychromatic418967fa.accept_19_6_8_2_1_6914 63 65 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 135 (accept_3_4 61 65 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 65 135 5 12 13 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 65 135
  (Polychromatic418967fa.accept_17_8_14_16_1_6849 59 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 135 (accept_3_4 58 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 65 135 5 11 13 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 65 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 65 135 (Polychromatic418967fa.accept_17_2_14_16_1_2187 53 65 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 135 (accept_3_4 52 65 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 65 135 (Polychromatic418967fa.accept_11_7_10_3_1_633 51 65 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 135 5 10 13 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 135 (accept_3_4 49 65 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 135 (Polychromatic418967fa.accept_18_12_11_9_1_4257 48 65
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 135
  (Polychromatic418967fa.accept_20_7_5_15_1_1548 47 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 135 (accept_3_4 46 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 65
  135 5 9 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  65 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 65 135 (accept_3_4 43 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 65 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 135 (Polychromatic418967fa.accept_20_1_5_15_1_6913 41 65
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 65 135 5 8 13 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 65 135
  (Polychromatic418967fa.accept_19_1_8_2_1_2876 39 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 65 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 135 (accept_3_4 37 65 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 65 135 (Polychromatic418967fa.accept_17_2_14_16_1_2187 36 65 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 135 5 7 13 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 135 (accept_3_4 34 65 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 65 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 135 (accept_3_4 31 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 65
  135 5 6 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  65 135 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 65 135 (accept_3_4 28 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 65 135 (Polychromatic418967fa.accept_20_7_5_15_1_1548 27 65 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 65 135 5 5 13 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 65 135
  (Polychromatic418967fa.accept_16_8_1_7_1_2355 24 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 65 135 (Polychromatic418967fa.accept_20_3_5_15_1_2644 23 65 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 135 (accept_3_4 22 65 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 65 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 65 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 135 5 4 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 135 (accept_3_4 19 65 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 135
  (Polychromatic418967fa.accept_20_17_5_15_1_6912 17 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 135 (accept_3_4 16 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 65
  135 5 3 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  65 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 65 135 (accept_3_4 13 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 65 135 (Polychromatic418967fa.accept_18_12_11_9_1_4257 12 65 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 135 (Polychromatic418967fa.accept_17_11_14_16_1_1270 11 65
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 65 135 5 2 13 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 65 135
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 65 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 135 (accept_3_4 7 65 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 65 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 135 5 1 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 135 (accept_3_4 4 65 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 135 (Polychromatic418967fa.accept_20_3_5_15_1_2644 3 65 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 135 (accept_3_4 1 65 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  135))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 135 (allA_succ_of_accept 63 64 135
  (Polychromatic418967fa.accept_17_12_13_16_1_3226 63 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 64 135 (accept_3_5 62 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 64 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 135 (Polychromatic418967fa.accept_13_8_12_5_1_1604 60 64
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 135 (accept_3_5 59 64 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 135 (Polychromatic418967fa.accept_13_6_12_5_1_2304
  58 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 135
  (Polychromatic418967fa.accept_14_1_8_9_1_1312 57 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 135 (accept_3_5 56 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 135 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 135 (accept_3_5 53 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 64 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 135
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 51 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 135 (accept_3_5 50 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 135 (accept_3_5 47 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 64 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 135
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 135 (accept_3_5 44 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 135 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 135 (accept_3_5 41 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 135 (Polychromatic418967fa.accept_13_1_12_5_1_1601 40 64 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 135
  (Polychromatic418967fa.accept_10_9_4_5_1_616 39 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 135 (accept_3_5 38 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 135 (accept_3_5 35 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 64 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 135
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 33 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 135 (accept_3_5 32 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 135 (Polychromatic418967fa.accept_12_6_4_3_1_361 30 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 135 (accept_3_5 29 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 135 (Polychromatic418967fa.accept_11_6_9_3_1_1103 28 64 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 135 (accept_3_5 26 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 135 (accept_3_5 23 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 135 (Polychromatic418967fa.accept_20_2_4_15_1_6911 22 64 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 135
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 135 (accept_3_5 20 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 135 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 135 (accept_3_5 17 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 64 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 135
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 135 (accept_3_5 14 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 135 (Polychromatic418967fa.accept_17_12_13_16_1_3226 12 64 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 135 (accept_3_5 11 64 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 64 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 135
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 135 (accept_3_5 8 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 64 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 135 (accept_3_5 5 64 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 135 (Polychromatic418967fa.accept_13_4_12_5_1_476 4 64 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  64 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 135 (accept_3_5 2 64 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  135)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 135 (allA_succ_of_accept 62 63 135
  (Polychromatic418967fa.accept_10_2_3_5_1_996 62 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 135 (Polychromatic418967fa.accept_11_6_8_3_1_2236 61 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 135 3 20 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 135 (Polychromatic418967fa.accept_13_7_11_5_1_2302
  59 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 135
  (Polychromatic418967fa.accept_10_8_3_5_1_613 58 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 135 3 19 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 135 (Polychromatic418967fa.accept_16_8_15_7_1_5658 56 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 135 (Polychromatic418967fa.accept_13_3_11_5_1_2348 55 63
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 135 9 6 7 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 135
  (Polychromatic418967fa.accept_19_15_6_2_1_6865 53 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 135 (Polychromatic418967fa.accept_10_2_3_5_1_996 52 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 135 3 17 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 135 (Polychromatic418967fa.accept_11_6_8_3_1_2236
  50 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 135
  (Polychromatic418967fa.accept_11_5_8_3_1_66 49 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 63 135 3 16 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 135 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 135 (Polychromatic418967fa.accept_13_7_11_5_1_2302 46 63
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 135 9 5 7 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 135
  (Polychromatic418967fa.accept_14_2_7_9_1_2937 44 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 135 (Polychromatic418967fa.accept_16_11_15_7_1_5654 43 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 135 3 14 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 135 (Polychromatic418967fa.accept_19_3_6_2_1_6910
  41 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 135
  (Polychromatic418967fa.accept_14_12_7_9_1_726 40 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 63 135 3 13 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 63 135 (Polychromatic418967fa.accept_10_8_3_5_1_613 38 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 135 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 63 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 135 9 4 7 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 135
  (Polychromatic418967fa.accept_16_3_15_7_1_3417 35 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 135 (Polychromatic418967fa.accept_19_15_6_2_1_6865 34 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 135 3 11 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 135 (Polychromatic418967fa.accept_10_2_3_5_1_996 32
  63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 135
  (Polychromatic418967fa.accept_19_12_6_2_1_5424 31 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 135 3 10 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 135 (Polychromatic418967fa.accept_13_3_11_5_1_2348 29 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 135 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 63 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 135 9 3 7 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 135
  (Polychromatic418967fa.accept_14_12_7_9_1_726 26 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 135 (Polychromatic418967fa.accept_20_5_3_15_1_6909 25 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 135 3 8 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 135 (Polychromatic418967fa.accept_19_4_6_2_1_6906 23 63 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 135
  (Polychromatic418967fa.accept_10_2_3_5_1_996 22 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 135 3 7 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 135 (Polychromatic418967fa.accept_13_7_11_5_1_2302 20 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 135 (Polychromatic418967fa.accept_13_6_11_5_1_133 19 63 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 135 9 2 7 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 135
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 135 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 135 3 5 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 135 (Polychromatic418967fa.accept_16_14_15_7_1_5655 14 63
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 135
  (Polychromatic418967fa.accept_17_13_12_16_1_6908 13 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 63 135 3 4 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 63 135 (Polychromatic418967fa.accept_16_11_15_7_1_5654 11 63 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 135
  (Polychromatic418967fa.accept_19_10_6_2_1_6907 10 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 135 9 1 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 135 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 135 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 63 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 135 3 2 21 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 135
  (Polychromatic418967fa.accept_11_5_8_3_1_66 5 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 135 (Polychromatic418967fa.accept_19_4_6_2_1_6906 4 63 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 135 3 1 21 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 135 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 63 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 135
  (Polychromatic418967fa.accept_17_1_12_16_1_2211 1 63 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 135))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 135 (allA_succ_of_accept
  61 62 135 (accept_3_4 61 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 135
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 62 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 135 (accept_3_4 58 62 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 135 (Polychromatic418967fa.accept_13_4_10_5_1_1644
  56 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 135 (accept_3_4 55
  62 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 135
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 54 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 135 (accept_3_4 52 62 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 135 (Polychromatic418967fa.accept_22_7_18_3_1_6905 51 62 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 135 (accept_3_4 49 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 135 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 135 (accept_3_4 46 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 135
  (Polychromatic418967fa.accept_20_4_2_15_1_6904 44 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 135 (accept_3_4 43 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 135 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 135 (accept_3_4 40 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 62 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 135
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 135 (accept_3_4 37 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 135 (accept_3_4 34 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 135
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 135 (accept_3_4 31 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 135 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 135 (accept_3_4 28 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 135 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 62 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 135
  (Polychromatic418967fa.accept_11_4_7_3_1_289 26 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 135 (accept_3_4 25 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 135 (accept_3_4 22 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 135
  (Polychromatic418967fa.accept_16_4_14_7_1_5641 20 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 135 (accept_3_4 19 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 135 (accept_3_4 16 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 62 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 135
  (Polychromatic418967fa.accept_17_14_11_16_1_3261 14 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 62 135 (accept_3_4 13 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 62 135 (Polychromatic418967fa.accept_17_12_11_16_1_6903 12 62 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 62 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 135 (accept_3_4 10 62 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 135 (accept_3_4 7 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  135 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 135 (accept_3_4 4 62 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 62 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 135 (Polychromatic418967fa.accept_13_2_10_5_1_1643
  2 62 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 135 (accept_3_4 1 62
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  135)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 135 (allA_succ_of_accept 60 61 135
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 135 (accept_3_5 59 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 135 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 135 (accept_3_5 56 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 135 (Polychromatic418967fa.accept_13_3_9_5_1_2340 55 61 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 135 (accept_3_5 53 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 135 (Polychromatic418967fa.accept_23_5_15_20_1_6902 51 61 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 135 (accept_3_5 50 61 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 61 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 135
  (Polychromatic418967fa.accept_26_22_9_5_1_6901 48 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 135 (accept_3_5 47 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 135 (accept_3_5 44 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 135 (Polychromatic418967fa.accept_13_4_9_5_1_1641 43 61 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 135 (accept_3_5 41 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 135 (accept_3_5 38 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 135 (Polychromatic418967fa.accept_19_18_4_2_1_2841 37 61 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 135
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 135 (accept_3_5 35 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 135 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 135 (accept_3_5 32 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 61 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 135 (accept_3_5 29 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 135 (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 135 (accept_3_5 26 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 61 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 135 (accept_3_5 23 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 135 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 135 (accept_3_5 20 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 61 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 135 (accept_3_5 17 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 135 (Polychromatic418967fa.accept_13_2_9_5_1_959 15 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 135 (accept_3_5 14 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 135 (Polychromatic418967fa.accept_29_13_3_19_1_6900 13 61 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 135
  (Polychromatic418967fa.accept_19_12_4_2_1_4121 12 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 135 (accept_3_5 11 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 135 (accept_3_5 8 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 135 (Polychromatic418967fa.accept_14_7_5_9_1_2911 7 61 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 135 (accept_3_5 5 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 61 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 135 (accept_3_5 2 61 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 135 (Polychromatic418967fa.accept_13_1_9_5_1_1598 1 61 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 135)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 135 (allA_succ_of_accept 59 60 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 60 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 135
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 58 60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 135 3 19 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 135 (Polychromatic418967fa.accept_16_8_12_7_1_2399 56 60 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 135 5 11 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 135 3 18 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 135 (Polychromatic418967fa.accept_13_1_8_5_1_2315
  53 60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 135
  (Polychromatic418967fa.accept_11_8_5_3_1_694 52 60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 60 135 3 17 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 60 135 5 10 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 135 (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 60 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 135 3 16 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 47
  60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 135
  (Polychromatic418967fa.accept_21_4_18_9_1_6899 46 60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 60 135 15 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 60 135 (Polychromatic418967fa.accept_14_2_4_9_1_2121 44 60 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 60 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 135 3 14 20 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 135
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 135 5 8 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 60 135 3 13 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 60 135 (Polychromatic418967fa.accept_13_12_8_5_1_976 38 60 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 135 (Polychromatic418967fa.accept_16_5_12_7_1_3411 37 60
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 135 3 12 20 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 135 5 7 12 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 135
  (Polychromatic418967fa.accept_7_6_4_2_1_236 34 60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 60 135 3 11 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 60 135 (Polychromatic418967fa.accept_18_14_6_9_1_1950 32 60 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 135 (Polychromatic418967fa.accept_18_13_6_9_1_4280 31 60
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 135 15 2 4 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 135
  (Polychromatic418967fa.accept_13_3_8_5_1_974 29 60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 135 (Polychromatic418967fa.accept_21_7_18_9_1_5291 28 60 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 135 3 9 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 60 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60 135 5 5 12 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 135 3 8 20 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 135
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 135 (Polychromatic418967fa.accept_21_1_18_9_1_5290 22 60 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 135 3 7 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 135 5 4 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 60 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 135 3 6 20 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 135
  (Polychromatic418967fa.accept_19_17_3_2_1_1725 17 60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 135 (Polychromatic418967fa.accept_13_3_8_5_1_974 16 60 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 135 15 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 135 (Polychromatic418967fa.accept_13_1_8_5_1_2315 14 60 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 135
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 135 3 4 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 135 5 2 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 135 3 3 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 135 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 60 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 135
  (Polychromatic418967fa.accept_18_7_6_9_1_4205 7 60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 135 3 2 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 60 135 5 1 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 60 135 (Polychromatic418967fa.accept_16_4_12_7_1_4475 4 60 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 135 3 1 20 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 135 (Polychromatic418967fa.accept_14_2_4_9_1_2121 2 60 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 135
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 1 60 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 135)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 135 (allA_succ_of_accept 58
  59 135 (accept_3_4 58 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 135 (accept_3_4 55 59 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 135 (Polychromatic418967fa.accept_16_5_11_7_1_5635
  53 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 135 (accept_3_4 52
  59 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 135
  (Polychromatic418967fa.accept_10_1_9_5_1_83 51 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 59 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 59 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 135 (accept_3_4 49 59 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 59 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 47
  59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 135 (accept_3_4 46 59
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 135
  (Polychromatic418967fa.accept_12_9_11_3_1_772 45 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 59 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 135 (accept_3_4 43 59 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 59 135 (Polychromatic418967fa.accept_28_14_3_23_1_6898 42 59 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 135 (accept_3_4 40 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 135 (Polychromatic418967fa.accept_21_18_17_9_1_6897 39 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 135 (accept_3_4 37 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 135
  (Polychromatic418967fa.accept_16_3_11_7_1_770 35 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 135 (accept_3_4 34 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 135 (accept_3_4 31 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 135 (Polychromatic418967fa.accept_18_12_5_9_1_6896 30 59 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 135 (accept_3_4 28 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 135 (accept_3_4 25 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 135 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 59 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 135
  (Polychromatic418967fa.accept_21_2_17_9_1_6895 23 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 135 (accept_3_4 22 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 135 (accept_3_4 19 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 135 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 59 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 135
  (Polychromatic418967fa.accept_20_17_19_15_1_6859 17 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 59 135 (accept_3_4 16 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 59 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 59 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 59 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 135 (accept_3_4 13 59 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 12
  59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 135
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 135 (accept_3_4 10 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 135 (accept_3_4 7 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 59 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 135 (accept_3_4 4 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  135 (Polychromatic418967fa.accept_16_3_11_7_1_770 3 59 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 135 (accept_3_4 1 59 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 135))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 135
  (allA_succ_of_accept 57 58 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 135 (accept_3_5 56 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 58 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 135 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  54 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 135 (accept_3_5 53
  58 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 135
  (Polychromatic418967fa.accept_10_2_8_5_1_587 52 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 135 (Polychromatic418967fa.accept_13_12_6_5_1_2335 51 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 135 (accept_3_5 50 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 135 (Polychromatic418967fa.accept_18_12_4_9_1_5452
  48 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 135 (accept_3_5 47
  58 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 135
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 46 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 58 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 135 (accept_3_5 44 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 58 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 58 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 135 (Polychromatic418967fa.accept_10_2_8_5_1_587
  42 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 135 (accept_3_5 41
  58 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 135
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 40 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 58 135 (Polychromatic418967fa.accept_14_11_2_9_1_5873 39 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 135 (accept_3_5 38 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 58 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 135 (Polychromatic418967fa.accept_13_10_6_5_1_2297
  36 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 135 (accept_3_5 35
  58 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 135
  (Polychromatic418967fa.accept_19_15_1_2_1_6894 34 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 58 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 135 (accept_3_5 32 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 58 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 58 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 135 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  30 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 135 (accept_3_5 29
  58 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 135
  (Polychromatic418967fa.accept_19_9_1_2_1_6839 28 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 58 135 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 135 (accept_3_5 26 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 58 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 135 (Polychromatic418967fa.accept_13_11_6_5_1_2339
  24 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 135 (accept_3_5 23
  58 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 135
  (Polychromatic418967fa.accept_10_2_8_5_1_587 22 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 58 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 135 (accept_3_5 20 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 58 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 58 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 135 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  18 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 135 (accept_3_5 17
  58 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 135
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 16 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 58 135 (Polychromatic418967fa.accept_18_15_4_9_1_4204 15 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 135 (accept_3_5 14 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 58 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 135 (Polychromatic418967fa.accept_10_2_8_5_1_587
  12 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 135 (accept_3_5 11
  58 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 135
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 58 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 135 (accept_3_5 8 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 58 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 58 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 135 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  6 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 135 (accept_3_5 5 58
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 135
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 58 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 135 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 135 (accept_3_5 2 58 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 135))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 57 135 (allA_succ_of_accept 56 57 135 (Polychromatic418967fa.accept_11_1_2_3_1_688 56 57 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 57 135 3 18 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 57 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 53 57 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 57 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 57 135 3 17 19 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 57 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 135 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 57 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 135 3 16 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 135 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 57 135 3 15 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 57 135 (Polychromatic418967fa.accept_17_10_6_16_1_6862 44 57 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 57 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 135 3 14 19 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 57 135 (Polychromatic418967fa.accept_16_8_9_7_1_768 40 57 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 135 3 13 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 135
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 57 135 3 12 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 57 135 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 57 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 135 3 11 19 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 135
  (Polychromatic418967fa.accept_10_2_7_5_1_605 32 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 57 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 135 3 10 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 135 (Polychromatic418967fa.accept_12_5_9_3_1_85 29
  57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 135
  (Polychromatic418967fa.accept_10_8_7_5_1_602 28 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 57 135 3 9 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 57 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 135 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 57 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 135 3 8 19 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 135
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 135 3 7 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 57 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 135
  (Polychromatic418967fa.accept_12_7_9_3_1_767 19 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 57 135 3 6 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 57 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 57 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 135 (Polychromatic418967fa.accept_21_16_15_9_1_6893 16 57
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 135 3 5 19 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 57 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 135 3 4 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 135 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 57 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 57 135 3 3 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 57 135 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 57 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 135 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 57 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 135 3 2 19 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 135
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 135 (Polychromatic418967fa.accept_21_4_15_9_1_3839 4 57 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 135 3 1 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 135
  (Polychromatic418967fa.accept_11_1_2_3_1_688 1 57 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 135))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 135 (allA_succ_of_accept 55 56
  135 (accept_3_4 55 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 56 135
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 56 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 135 (accept_3_4 52 56 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 56 135 (Polychromatic418967fa.accept_10_1_6_5_1_304 51 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 135
  (Polychromatic418967fa.accept_20_10_16_15_1_1536 50 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 56 135 (accept_3_4 49 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 56 135 (Polychromatic418967fa.accept_13_9_4_5_1_1651 48 56 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 56 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 135 (accept_3_4 46 56 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 135 (Polychromatic418967fa.accept_13_6_4_5_1_2330
  45 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 135
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 135 (accept_3_4 43 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 135 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 135 (accept_3_4 40 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 135 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 56 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 135
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 38 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 135 (accept_3_4 37 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 135 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 135 (accept_3_4 34 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 135 (Polychromatic418967fa.accept_16_1_8_7_1_3377 33 56 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 135
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 32 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 135 (accept_3_4 31 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 135 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 135 (accept_3_4 28 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 135 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 56 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 135
  (Polychromatic418967fa.accept_21_5_14_9_1_2410 26 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 135 (accept_3_4 25 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 135 (accept_3_4 22 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 135 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 56 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 135
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 20 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 135 (accept_3_4 19 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 135 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 135 (accept_3_4 16 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 135 (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 56 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 135
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 135 (accept_3_4 13 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 135 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 135 (accept_3_4 10 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 135 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 56 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 135
  (Polychromatic418967fa.accept_26_8_4_5_1_6892 8 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 135 (accept_3_4 7 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  135 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 135 (accept_3_4 4 56 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 135 (Polychromatic418967fa.accept_18_3_2_9_1_1013 3 56 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 135 (Polychromatic418967fa.accept_11_2_1_3_1_683 2
  56 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 135 (accept_3_4 1 56 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 135))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 135 (allA_succ_of_accept 54 55 135 (Polychromatic418967fa.accept_13_2_3_5_1_2294 54 55 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 135 (accept_3_5 53 55 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 135
  (Polychromatic418967fa.accept_29_22_26_19_1_6891 51 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 55 135 5 10 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 55 135 (Polychromatic418967fa.accept_17_15_4_16_1_6890 49 55 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 135
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 48 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 135 (accept_3_5 47 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 55 135 5 9 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 55 135 (accept_3_5 44 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 55 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 55 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 135 (Polychromatic418967fa.accept_18_6_1_9_1_5551 42 55 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 135 (accept_3_5 41 55 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55 135 5 8 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 55 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 39
  55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 135 (accept_3_5 38 55
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 135
  (Polychromatic418967fa.accept_13_11_3_5_1_982 37 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 55 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 55 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 135 5 7 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 55 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 135
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 135 (accept_3_5 32 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 55 135 5 6 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 55 135 (accept_3_5 29 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 55 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 135 (Polychromatic418967fa.accept_13_1_3_5_1_140 27 55 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 135 (accept_3_5 26 55 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55 135 5 5 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 55 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 24
  55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 135 (accept_3_5 23 55
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 135 (Polychromatic418967fa.accept_6_4_1_3_1_77
  22 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 135
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 55 135 5 4 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 55 135 (Polychromatic418967fa.accept_13_6_3_5_1_3167 19 55 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 55 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 135 (accept_3_5 17 55 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 135 5 3 11 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 135 (accept_3_5 14
  55 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 135
  (Polychromatic418967fa.accept_22_13_11_3_1_6889 13 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 55 135 (Polychromatic418967fa.accept_19_12_17_2_1_6888 12 55 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 135 (accept_3_5 11 55 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 55 135 5 2 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 55 135 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 55 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 135 (accept_3_5 8 55 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 135 (Polychromatic418967fa.accept_19_7_17_2_1_6855 7 55 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 135
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 6 55 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 55 135 5 1 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 55 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 55 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 135 (accept_3_5 2 55 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 55
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  135))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 135 (allA_succ_of_accept 53 54 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 54 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 54 135 3 17 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 54 135 (Polychromatic418967fa.accept_12_2_6_3_1_331 50
  54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 135 3 16 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 135 (Polychromatic418967fa.accept_16_15_6_7_1_4512 47 54 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 54 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 135 9 5 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 135
  (Polychromatic418967fa.accept_12_8_6_3_1_366 44 54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 135 (Polychromatic418967fa.accept_13_4_2_5_1_4045 43 54 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 135 3 14 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 135
  (Polychromatic418967fa.accept_11_7_10_3_1_633 40 54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 54 135 3 13 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 54 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 54 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 135 9 4 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 135
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 35 54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 135 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 54 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 135 3 11 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 135 3 10 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 135 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 54 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 135 27 1 2 5 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 135
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 135 3 8 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 135 (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 54 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 135
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 54 135 3 7 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 54 135 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 54 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 135 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 54 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 135 9 2 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 54 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 135 3 5 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 135 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 54 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 135 3 4 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 54 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 54 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 135 9 1 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 135
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 135 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 54 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 135 3 2 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 135
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 54 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 54 135 3 1 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 54 135 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 54 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  135)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 135 (allA_succ_of_accept 52 53 135 (accept_3_4
  52 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 135
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 51 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 135 (accept_3_4 49 53 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 53 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 47
  53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 135 (accept_3_4 46 53
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 135
  (Polychromatic418967fa.accept_12_9_5_3_1_782 45 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 135 (accept_3_4 43 53 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 41
  53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 135 (accept_3_4 40 53
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 135
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 135 (accept_3_4 37 53 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 135 (Polychromatic418967fa.accept_19_17_15_2_1_6887 36 53 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 135
  (Polychromatic418967fa.accept_13_9_1_5_1_964 35 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 135 (accept_3_4 34 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 135 (accept_3_4 31 53 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 135
  (Polychromatic418967fa.accept_13_3_1_5_1_499 29 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 135 (accept_3_4 28 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 135 (accept_3_4 25 53 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 135 (Polychromatic418967fa.accept_30_24_23_15_1_6886 24 53 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 135
  (Polychromatic418967fa.accept_21_2_11_9_1_2534 23 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 135 (accept_3_4 22 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 135 (accept_3_4 19 53 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 135
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 135 (accept_3_4 16 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 135 (Polychromatic418967fa.accept_18_15_17_9_1_4200 15 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 135 (accept_3_4 13 53 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 135
  (Polychromatic418967fa.accept_16_11_5_7_1_2395 11 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 135 (accept_3_4 10 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 135 (accept_3_4 7 53 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 135
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 135 (accept_3_4 4 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  135 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 53 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 135 (accept_3_4 1 53 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 135))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 135
  (allA_succ_of_accept 51 52 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 135 (accept_3_5 50 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 48
  52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 135 (accept_3_5 47 52
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 135
  (Polychromatic418967fa.accept_16_14_4_7_1_2380 46 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 52 135 (Polychromatic418967fa.accept_16_13_4_7_1_1537 45 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 135 (accept_3_5 44 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 52 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 135 (Polychromatic418967fa.accept_12_6_4_3_1_361
  42 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 135 (accept_3_5 41
  52 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 52 135 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 135 (accept_3_5 38 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 52 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 36
  52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 135 (accept_3_5 35 52
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 52 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 135 (accept_3_5 32 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 52 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 135 (Polychromatic418967fa.accept_12_6_4_3_1_361
  30 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 135 (accept_3_5 29
  52 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 135
  (Polychromatic418967fa.accept_10_8_2_5_1_596 28 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 52 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 135 (accept_3_5 26 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 52 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 135 (Polychromatic418967fa.accept_16_8_4_7_1_3390
  24 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 135 (accept_3_5 23
  52 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 22 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 52 135 (Polychromatic418967fa.accept_30_21_22_15_1_1027 21 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 135 (accept_3_5 20 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 52 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 135 (Polychromatic418967fa.accept_10_8_2_5_1_596
  18 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 135 (accept_3_5 17
  52 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 135
  (Polychromatic418967fa.accept_11_5_8_3_1_66 16 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 52 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 135 (accept_3_5 14 52 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 52 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 12
  52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 135 (accept_3_5 11 52
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 135
  (Polychromatic418967fa.accept_20_10_12_15_1_3940 10 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 135 (Polychromatic418967fa.accept_23_9_6_20_1_5202 9 52 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 135 (accept_3_5 8 52 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 135 (accept_3_5 5 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  135 (Polychromatic418967fa.accept_19_4_14_2_1_4117 4 52 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 52 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 52 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 135 (accept_3_5 2 52 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  135)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 135 (allA_succ_of_accept 50 51 135
  (Polychromatic418967fa.accept_20_10_11_15_1_6885 50 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 51 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 51 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 135 3 16 17 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 135
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 47 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 51 135 (Polychromatic418967fa.accept_10_6_1_5_1_1024 46 51 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 135 3 15 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 135 (Polychromatic418967fa.accept_8_4_3_7_1_491 44
  51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 135
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 43 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 51 135 3 14 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 51 135 (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 51 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 135 (Polychromatic418967fa.accept_13_1_12_5_1_1601 40 51
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 135 3 13 17 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 135
  (Polychromatic418967fa.accept_22_16_7_3_1_6884 38 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 135 (Polychromatic418967fa.accept_11_4_7_3_1_289 37 51 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 135 3 12 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 135 (Polychromatic418967fa.accept_18_17_15_9_1_5542
  35 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 135
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 34 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 51 135 3 11 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 51 135 (Polychromatic418967fa.accept_11_10_7_3_1_3679 32 51 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 135 (Polychromatic418967fa.accept_16_15_3_7_1_3389 31 51
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 135 3 10 17 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 135
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 135 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 51 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 135 3 9 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 135 (Polychromatic418967fa.accept_10_6_1_5_1_1024 26 51 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 135
  (Polychromatic418967fa.accept_16_9_3_7_1_6883 25 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 51 135 3 8 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 51 135 (Polychromatic418967fa.accept_18_5_15_9_1_1919 23 51 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 135 (Polychromatic418967fa.accept_18_4_15_9_1_6882 22 51
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 135 3 7 17 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 135
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 51 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 135 3 6 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 135 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 51 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 135
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 51 135 3 5 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 135 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 51 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 135 (Polychromatic418967fa.accept_20_13_11_15_1_6881 13 51
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 135 3 4 17 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 135
  (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 135 (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 51 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 135 3 3 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 135 (Polychromatic418967fa.accept_13_8_12_5_1_1604 8 51 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 135
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 135 3 2 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 135 (Polychromatic418967fa.accept_18_5_15_9_1_1919 5 51 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 135 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 51 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 135 3 1 17 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 135
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 2 51 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 135 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 51 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 51 135))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 135
  (allA_succ_of_accept 49 50 135 (accept_3_4 49 50 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  50 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 50 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 50 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 50 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 135 (accept_3_4 46 50 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 45 50 135 5 9 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 50 135 (Polychromatic418967fa.accept_16_12_2_7_1_6853 44 50 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 135 (accept_3_4 43 50 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 135 (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 50 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 50 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 135 5 8 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 135 (Polychromatic418967fa.accept_18_3_14_9_1_4264 39 50 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 50 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 135 (accept_3_4 37 50 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 135
  (Polychromatic418967fa.accept_19_17_12_2_1_6880 36 50 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 50 135 5 7 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 50 135 (accept_3_4 34 50 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  50 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 50 135 (Polychromatic418967fa.accept_13_6_11_5_1_133 32 50 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 135 (accept_3_4 31 50 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 135 5 6 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 50 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 135 (accept_3_4 28 50 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 50 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 135
  (Polychromatic418967fa.accept_20_6_10_15_1_6879 26 50 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 50 135 5 5 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 50 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 50 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 50 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 135 (accept_3_4 22 50 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  50 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 135 5 4 10 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 135 (accept_3_4 19
  50 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 135
  (Polychromatic418967fa.accept_12_6_2_3_1_354 18 50 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 135 (accept_3_4 16 50 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 50 135 5 3 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 50 135 (Polychromatic418967fa.accept_19_14_12_2_1_6878 14 50 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 135 (accept_3_4 13 50 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 135 (Polychromatic418967fa.accept_16_12_2_7_1_6853 12 50
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 135
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 135 5 2 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 135 (Polychromatic418967fa.accept_11_8_6_3_1_661 8 50 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 135 (accept_3_4 7 50 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  50 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 50 135 5 1 10 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 50 135 (accept_3_4 4 50
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 135 (Polychromatic418967fa.accept_7_3_1_2_1_247
  3 50 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 135
  (Polychromatic418967fa.accept_20_2_10_15_1_3953 2 50 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 135 (accept_3_4 1 50 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  135)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 135 (allA_succ_of_accept 48 49 135
  (Polychromatic418967fa.accept_17_14_15_16_1_1271 48 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 49 135 (accept_3_5 47 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 49 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 135 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 49 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 135 (accept_3_5 44 49 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 135 (Polychromatic418967fa.accept_13_4_10_5_1_1644
  43 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 135 (accept_3_5 41 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 135 (Polychromatic418967fa.accept_18_3_13_9_1_4260 39 49 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 135 (accept_3_5 38 49 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 135 (Polychromatic418967fa.accept_21_16_7_9_1_6877 37 49
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 135
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 135 (accept_3_5 35 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 135 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 49 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 135 (accept_3_5 32 49 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 49 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 135 (accept_3_5 29 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 135 (Polychromatic418967fa.accept_19_8_11_2_1_6876 27 49 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 135 (accept_3_5 26 49 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 135 (Polychromatic418967fa.accept_20_5_9_15_1_3973 25 49
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 135
  (Polychromatic418967fa.accept_10_4_9_5_1_84 24 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 135 (accept_3_5 23 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 49 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 135 (accept_3_5 20 49 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 135 (Polychromatic418967fa.accept_11_8_5_3_1_694 19 49 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 135 (accept_3_5 17 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 135 (Polychromatic418967fa.accept_13_2_10_5_1_1643 15 49 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 135 (accept_3_5 14 49 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 135 (Polychromatic418967fa.accept_19_13_11_2_1_4112 13 49
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 135
  (Polychromatic418967fa.accept_14_12_7_9_1_726 12 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 135 (accept_3_5 11 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 135 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 49 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 135 (accept_3_5 8 49 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 135 (Polychromatic418967fa.accept_28_7_21_23_1_6875 7 49 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 135 (accept_3_5 5 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 135 (Polychromatic418967fa.accept_18_3_13_9_1_4260 3 49 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 135 (accept_3_5 2 49 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 49 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 135))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 135 (allA_succ_of_accept 47 48 135 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 48 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 46
  48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 135 3 15 16 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 135
  (Polychromatic418967fa.accept_19_6_10_2_1_6874 44 48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 48 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 135 3 14 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 135 (Polychromatic418967fa.accept_13_2_9_5_1_959 41
  48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 135
  (Polychromatic418967fa.accept_11_7_4_3_1_302 40 48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 48 135 3 13 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 48 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 48 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 135 (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 48 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 135 3 12 16 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 135
  (Polychromatic418967fa.accept_18_17_12_9_1_3031 35 48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 135 (Polychromatic418967fa.accept_18_16_12_9_1_5504 34 48 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 135 3 11 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 32
  48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 135
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 135 3 10 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 48 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 135 (Polychromatic418967fa.accept_13_2_9_5_1_959 28 48 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 135 3 9 16 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 135
  (Polychromatic418967fa.accept_23_3_2_20_1_6873 26 48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 48 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 135 3 8 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 135 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 48 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 22 48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 48 135 3 7 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 48 135 (Polychromatic418967fa.accept_21_20_6_9_1_6872 20 48 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 135 (Polychromatic418967fa.accept_17_2_14_16_1_2187 19 48
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 135 3 6 16 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 135
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 135 (Polychromatic418967fa.accept_13_3_9_5_1_2340 16 48 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 135 3 5 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 135 (Polychromatic418967fa.accept_13_1_9_5_1_1598 14 48 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 135
  (Polychromatic418967fa.accept_10_3_8_5_1_606 13 48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 135 3 4 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 48 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 135 3 3 16 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 135 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 48 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 135 3 2 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 135 (Polychromatic418967fa.accept_18_5_12_9_1_6871 5 48 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 135
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 48 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 48 135 3 1 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 48 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 48 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 48 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  135)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 135 (allA_succ_of_accept 46 47 135 (accept_3_4 46 47
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 135 (Polychromatic418967fa.accept_7_3_5_2_1_17
  45 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 135 (accept_3_4 43 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 135 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 135 (Polychromatic418967fa.accept_20_1_7_15_1_1521 41 47 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 135 (accept_3_4 40 47 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 47 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 135 (accept_3_4 37 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 135 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 135 (Polychromatic418967fa.accept_14_7_5_9_1_2911 35 47 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 135 (accept_3_4 34 47 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 47 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 135 (accept_3_4 31 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 135 (Polychromatic418967fa.accept_16_14_15_7_1_5655 30 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 135 (Polychromatic418967fa.accept_13_3_8_5_1_974 29 47 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 135 (accept_3_4 28 47 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 135 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 47 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 135 (accept_3_4 25 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 47 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 135 (accept_3_4 22 47 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 47 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 135 (accept_3_4 19 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 47 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 135 (accept_3_4 16 47 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 135 (Polychromatic418967fa.accept_18_15_11_9_1_4256 15 47 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 135 (accept_3_4 13 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 135 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 47 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 135 (accept_3_4 10 47 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 47 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 135 (accept_3_4 7 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  135 (Polychromatic418967fa.accept_16_6_15_7_1_1510 6 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 47 135 (Polychromatic418967fa.accept_20_5_7_15_1_2668 5 47 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 135 (accept_3_4 4 47 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 47 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 135 (accept_3_4 1 47 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  135))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 135 (allA_succ_of_accept 45 46 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 135 (accept_3_5 44 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 135 (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 46 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 135 (accept_3_5 41 46 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 46 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 135
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 135 (accept_3_5 38 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 135 (Polychromatic418967fa.accept_16_4_14_7_1_5641 36 46 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 135 (accept_3_5 35 46 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 46 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 135 (accept_3_5 32 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 135 (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 46 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 135 (accept_3_5 29 46 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 135 (Polychromatic418967fa.accept_13_2_7_5_1_3189 28 46 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 135
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 135 (accept_3_5 26 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 46 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 135 (accept_3_5 23 46 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 135 (Polychromatic418967fa.accept_25_22_21_10_1_6870 22 46 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 135 (accept_3_5 20 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 135 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 46 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 135 (accept_3_5 17 46 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 135 (Polychromatic418967fa.accept_14_2_4_9_1_2121 16 46 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 135
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 15 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 135 (accept_3_5 14 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 46 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 135 (accept_3_5 11 46 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 135 (Polychromatic418967fa.accept_16_10_14_7_1_2372 10 46 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 135 (accept_3_5 8 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 46 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 135 (accept_3_5 5 46 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 46 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 135 (Polychromatic418967fa.accept_24_3_22_15_1_1938
  3 46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 135 (accept_3_5 2 46
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  46 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  135)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 135 (allA_succ_of_accept 44 45 135
  (Polychromatic418967fa.accept_20_4_5_15_1_6869 44 45 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 45 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 135 3 14 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 41
  45 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 135 5 8 9 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 45 135 3 13 15 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 135 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 45 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 135 9 4 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 45 135 5 7 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 135 3 11 15 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 135
  (Polychromatic418967fa.accept_17_15_11_16_1_3263 32 45 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 45 135 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 45 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 135 15 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 29
  45 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 135
  (Polychromatic418967fa.accept_19_9_7_2_1_6868 28 45 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 135 9 3 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 135 5 5 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 45 135 3 8 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 135 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 45 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 135 3 7 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 45 135 5 4 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 45 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 135 9 2 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 135 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 45 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 135
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 16 45 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 45 135 15 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 45 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 45 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 135 3 4 15 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 135
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 45 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 45 135 5 2 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 45 135 9 1 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 45 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 135 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 45 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 135 3 2 15 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 45 135 5 1 9 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 135
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 45 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 135 3 1 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 45 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  135))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 135 (allA_succ_of_accept 43 44 135 (accept_3_4 43 44
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 135
  (Polychromatic418967fa.accept_12_6_8_3_1_82 42 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 135 (accept_3_4 40 44 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 135 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 44 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 135 (Polychromatic418967fa.accept_21_17_2_9_1_6867
  38 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 135 (accept_3_4 37
  44 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 135
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 135 (accept_3_4 34 44 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 135 (Polychromatic418967fa.accept_21_12_2_9_1_6866 33 44 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 135
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 32 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 135 (accept_3_4 31 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 135 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 135 (accept_3_4 28 44 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 44 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 135
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 135 (accept_3_4 25 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 135 (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 135 (accept_3_4 22 44 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 135 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 44 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 135
  (Polychromatic418967fa.accept_16_4_12_7_1_4475 20 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 135 (accept_3_4 19 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 135 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 135 (accept_3_4 16 44 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 135 (Polychromatic418967fa.accept_19_15_6_2_1_6865 15 44 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 135
  (Polychromatic418967fa.accept_21_14_2_9_1_6864 14 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 135 (accept_3_4 13 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 135 (Polychromatic418967fa.accept_19_12_6_2_1_5424 12 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 135 (accept_3_4 10 44 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 135 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 44 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 135
  (Polychromatic418967fa.accept_16_8_12_7_1_2399 8 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 135 (accept_3_4 7 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  135 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 135 (accept_3_4 4 44 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 44 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 135 (Polychromatic418967fa.accept_16_2_12_7_1_3410
  2 44 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 135 (accept_3_4 1 44
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 135)))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  43 135 (allA_succ_of_accept 42 43 135 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 43 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 135 (accept_3_5 41 43 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 135
  (Polychromatic418967fa.accept_18_3_7_9_1_5486 39 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 135 (accept_3_5 38 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 135 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 135 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 43 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 135 (accept_3_5 35 43 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 43 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 135
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 135 (accept_3_5 32 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 135 (Polychromatic418967fa.accept_17_13_9_16_1_3254 30 43 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 135 (accept_3_5 29 43 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 135 (accept_3_5 26 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 135 (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 43 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 135 (accept_3_5 23 43 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 43 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 135
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 135 (accept_3_5 20 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 135 (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 135 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 43 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 135 (accept_3_5 17 43 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 135
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 135 (accept_3_5 14 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 135 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 43 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 135 (accept_3_5 11 43 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 43 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 135
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 135 (accept_3_5 8 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  135 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 43 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 135 (accept_3_5 5 43 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 135 (accept_3_5 2 43 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 135 (Polychromatic418967fa.accept_13_1_4_5_1_113 1
  43 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  135))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 135 (allA_succ_of_accept 41 42 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 135 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 42 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 135 3 13 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 135 (Polychromatic418967fa.accept_10_8_2_5_1_596 38
  42 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 135 3 12 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 135 (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 42 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 135 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 42 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 135 3 11 14 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 135
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 42 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 135 (Polychromatic418967fa.accept_17_14_8_16_1_6863 31 42 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 135 3 10 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 135
  (Polychromatic418967fa.accept_10_8_2_5_1_596 28 42 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 42 135 3 9 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 42 135 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 42 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 135 3 8 14 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 135
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 42 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 135 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 42 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 135 3 7 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 135 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 42 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 135
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 19 42 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 135 3 6 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 135 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 42 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 135 3 5 14 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 42 135
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 42 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 42 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 135 3 4 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 135 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 42 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 135
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 42 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 42 135 3 3 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 42 135 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 42 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 135 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 42 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 135 3 2 14 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 135 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 42 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 135 3 1 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 135 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 42 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 135)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 135 (allA_succ_of_accept 40 41 135
  (accept_3_4 40 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 135
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 135 (accept_3_4 37 41 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 135 (Polychromatic418967fa.accept_13_9_2_5_1_2310
  35 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 135 (accept_3_4 34
  41 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 135
  (Polychromatic418967fa.accept_12_9_5_3_1_782 33 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 135 (accept_3_4 31 41 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 135 (accept_3_4 28 41
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 135
  (Polychromatic418967fa.accept_11_5_8_3_1_66 27 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 41 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 135 (accept_3_4 25 41 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 41 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 135 (Polychromatic418967fa.accept_13_10_2_5_1_1633
  23 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 135 (accept_3_4 22
  41 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 135
  (Polychromatic418967fa.accept_12_9_5_3_1_782 21 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 135 (accept_3_4 19 41 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 17
  41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 135 (accept_3_4 16 41
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 135 (Polychromatic418967fa.accept_7_1_6_2_1_18
  15 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 135 (accept_3_4 13 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 135 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 41 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 135 (accept_3_4 10 41 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 41 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 135 (accept_3_4 7 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 135 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 41 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 135 (accept_3_4 4 41 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 41 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 135 (accept_3_4 1 41 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 135))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 135
  (allA_succ_of_accept 39 40 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 40 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 40 135 (accept_3_5 38 40 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 40 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 40 135 (Polychromatic418967fa.accept_16_4_8_7_1_3396
  36 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 40 135 5 7 8 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 40 135
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 34 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 40 135 (Polychromatic418967fa.accept_16_1_8_7_1_3377 33 40 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 135 (accept_3_5 32 40 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 40 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 135 5 6 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 135 (accept_3_5 29 40 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 135 (Polychromatic418967fa.accept_16_12_8_7_1_4530 28 40 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 135
  (Polychromatic418967fa.accept_17_10_6_16_1_6862 27 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 135 (accept_3_5 26 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 40
  135 5 5 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  40 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 40 135 (accept_3_5 23 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 40 135 (Polychromatic418967fa.accept_13_9_1_5_1_964 22 40 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 135 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 40
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 135 5 4 8 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 135
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 40 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 40 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 135 (accept_3_5 17 40 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 40 135 (Polychromatic418967fa.accept_13_3_1_5_1_499 16 40 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 40 135 5 3 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 40 135 (accept_3_5 14 40 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 135
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 135 (accept_3_5 11 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  135 5 2 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40
  135 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 135 (accept_3_5 8 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 135 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 40 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 40 135 5 1 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 40 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 40 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 135 (accept_3_5 2 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40
  135 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 135)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 135 (allA_succ_of_accept 38 39 135
  (Polychromatic418967fa.accept_17_4_5_16_1_3240 38 39 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 135 (Polychromatic418967fa.accept_18_1_3_9_1_328 37 39 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 135 3 12 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 135 (Polychromatic418967fa.accept_17_1_5_16_1_5589
  35 39 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 135
  (Polychromatic418967fa.accept_7_6_4_2_1_236 34 39 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 135 3 11 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 135 (Polychromatic418967fa.accept_18_14_3_9_1_4234 32 39 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 39 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 135 3 10 13 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 135
  (Polychromatic418967fa.accept_21_8_18_9_1_5329 29 39 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 135 (Polychromatic418967fa.accept_17_11_5_16_1_5600 28 39 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 135 3 9 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 39 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 135
  (Polychromatic418967fa.accept_18_7_3_9_1_1020 25 39 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 135 3 8 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 135 (Polychromatic418967fa.accept_25_23_14_10_1_6861 23 39 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 135 (Polychromatic418967fa.accept_19_3_1_2_1_6860 22 39 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 135 3 7 13 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 135
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 39 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 39 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 135 3 6 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 135 (Polychromatic418967fa.accept_20_17_19_15_1_6859 17 39
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 135
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 39 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 135 3 5 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 135 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 39 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 39 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 135 3 4 13 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 135
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 39 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 135 (Polychromatic418967fa.accept_20_10_19_15_1_2692 10 39 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 135 3 3 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 135 (Polychromatic418967fa.accept_11_8_6_3_1_661 8 39 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 135
  (Polychromatic418967fa.accept_18_7_3_9_1_1020 7 39 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 135 3 2 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 39 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 135 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 39 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 135 3 1 13 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 135
  (Polychromatic418967fa.accept_14_2_11_9_1_2925 2 39 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 39 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 135))))))))))))))))))))))))))))))))))))))) (allB_succ 38 135
  (allA_succ_of_accept 37 38 135 (accept_3_4 37 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 38 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 135 (accept_3_4 34 38 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 135
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 135 (accept_3_4 31 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 135 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 135 (accept_3_4 28 38 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 38 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 135 (accept_3_4 25 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 135 (Polychromatic418967fa.accept_18_6_2_9_1_3056 24 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 135 (accept_3_4 22 38 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 135 (accept_3_4 19 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 135 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 135 (accept_3_4 16 38 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 38 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 135
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 14 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 135 (accept_3_4 13 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 38 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 135 (accept_3_4 10 38 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 135 (accept_3_4 7 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  135 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 38 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 135 (accept_3_4 4 38 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 135 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 38 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  38 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 135 (accept_3_4 1 38 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 135)))))))))))))))))))))))))))))))))))))) (allB_succ 37 135
  (allA_succ_of_accept 36 37 135 (Polychromatic418967fa.accept_21_15_16_9_1_5303 36 37 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 135 (accept_3_5 35 37 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 135 (Polychromatic418967fa.accept_10_3_7_5_1_288
  33 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 135 (accept_3_5 32
  37 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 135
  (Polychromatic418967fa.accept_21_10_16_9_1_5302 31 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 135 (accept_3_5 29 37 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 135 (Polychromatic418967fa.accept_16_11_5_7_1_2395
  27 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 135 (accept_3_5 26
  37 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 135
  (Polychromatic418967fa.accept_20_5_17_15_1_6858 25 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 135 (Polychromatic418967fa.accept_17_7_3_16_1_2208 24 37 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 135 (accept_3_5 23 37 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 135 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 135 (accept_3_5 20
  37 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 135
  (Polychromatic418967fa.accept_13_6_11_5_1_133 19 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 135 (accept_3_5 17 37 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 135
  (Polychromatic418967fa.accept_19_15_18_2_1_6857 15 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 135 (accept_3_5 14 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 135 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 37 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 135 (accept_3_5 11 37 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 135
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 135 (accept_3_5 8 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  135 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 135 (accept_3_5 5 37 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 3
  37 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 135 (accept_3_5 2 37 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 135 (Polychromatic418967fa.accept_19_1_18_2_1_2835
  1 37 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  135))))))))))))))))))))))))))))))))))))) (allB_succ 36 135 (allA_succ_of_accept 35 36 135
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 36 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 135 3 11 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 135 (Polychromatic418967fa.accept_13_6_10_5_1_1648
  32 36 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 135
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 36 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 135 3 10 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 135 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 36 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 135 (Polychromatic418967fa.accept_13_2_10_5_1_1643 28 36
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 36 135 9 3 4 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 135
  (Polychromatic418967fa.accept_19_7_17_2_1_6855 26 36 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 135 (Polychromatic418967fa.accept_17_8_2_16_1_5598 25 36 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 135 3 8 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 135 (Polychromatic418967fa.accept_19_4_17_2_1_5409 23 36 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 135
  (Polychromatic418967fa.accept_17_5_2_16_1_1294 22 36 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 36 135 3 7 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 36 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 36 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 36 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 135 9 2 4 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 135
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 135 (Polychromatic418967fa.accept_19_16_17_2_1_6856 16 36 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 135 3 5 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 36 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 36 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 135 3 4 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 36 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 36 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 135 9 1 4 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 135
  (Polychromatic418967fa.accept_13_8_10_5_1_977 8 36 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 135 (Polychromatic418967fa.accept_19_7_17_2_1_6855 7 36 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 135 3 2 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 135 (Polychromatic418967fa.accept_17_5_2_16_1_1294 5 36 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 135
  (Polychromatic418967fa.accept_10_4_6_5_1_74 4 36 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 36 135 3 1 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 36 135 (Polychromatic418967fa.accept_13_2_10_5_1_1643 2 36 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 135 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 36 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 135))))))))))))))))))))))))))))))))))))
  (allB_succ 35 135 (allA_succ_of_accept 34 35 135 (accept_3_4 34 35 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 35 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 135 (accept_3_4 31 35 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 35 135 5 6 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 35 135 (Polychromatic418967fa.accept_13_3_9_5_1_2340
  29 35 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 135 (accept_3_4 28
  35 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 135
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 35 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 35 135 5 5 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 35 135 (Polychromatic418967fa.accept_19_5_16_2_1_1717 24 35 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 135
  (Polychromatic418967fa.accept_11_1_2_3_1_688 23 35 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 135 (accept_3_4 22 35 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 35 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 35 135 5 4 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 35 135 (accept_3_4 19 35 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 35 135 (Polychromatic418967fa.accept_19_18_16_2_1_2858 18 35 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 135 (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 35 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 135 (accept_3_4 16 35 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 35 135 5 3 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 35 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 14
  35 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 135 (accept_3_4 13 35
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 135
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 35 135 (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 35 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 35 135 5 2 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 35 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 35 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 135 (accept_3_4 7 35 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  135 (Polychromatic418967fa.accept_21_6_14_9_1_6854 6 35 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 35 135 5 1 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 35 135 (accept_3_4 4 35 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 35 135 (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 35 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 135 (accept_3_4 1 35 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 135))))))))))))))))))))))))))))))))))) (allB_succ 34 135
  (allA_succ_of_accept 33 34 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 135 (accept_3_5 32 34 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 34 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 34 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 135 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  30 34 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 135 (accept_3_5 29
  34 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 135
  (Polychromatic418967fa.accept_16_12_2_7_1_6853 28 34 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 34 135 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 34 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 34 135 (accept_3_5 26 34 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 34 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 34 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 24
  34 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 135 (accept_3_5 23 34
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 135 (Polychromatic418967fa.accept_7_1_6_2_1_18
  22 34 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 135 (accept_3_5 20 34 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 34 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 34 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 135 (accept_3_5 17 34 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 34 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 135
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 34 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 135 (accept_3_5 14 34 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 135 (Polychromatic418967fa.accept_13_12_8_5_1_976 12 34 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 135 (accept_3_5 11 34 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 34 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 135 (accept_3_5 8 34 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 34 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 135 (accept_3_5 5 34 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 34 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 34
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 135 (accept_3_5 2 34 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 135))))))))))))))))))))))))))))))))))
  (allB_succ 33 135 (allA_succ_of_accept 32 33 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 33 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 33 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 135 3 10 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 135 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 33 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 135 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 33 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 135 3 9 11 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 33 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 135 3 8 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 135 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 33 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 135 3 7 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 135 (Polychromatic418967fa.accept_19_1_14_2_1_4134 20 33 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 135 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 33 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 135 3 6 11 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 33 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 135 (Polychromatic418967fa.accept_18_16_15_9_1_6852 16 33 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 135 3 5 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 135
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 33 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 135 3 4 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 33 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 135 3 3 11 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 135
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 33 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 135 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 33 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 135 3 2 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 135 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 33 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 135
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 33 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 135 3 1 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 135 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 33 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 135)))))))))))))))))))))))))))))))))
  (allB_succ 32 135 (allA_succ_of_accept 31 32 135 (accept_3_4 31 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 135 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 32 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 135 (accept_3_4 28 32 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 27
  32 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 135
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 135 (accept_3_4 25 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 135 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 135 (accept_3_4 22 32 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 135 (Polychromatic418967fa.accept_17_4_15_16_1_3231 21 32 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 135
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 135 (accept_3_4 19 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 135 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 135 (accept_3_4 16 32 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 135 (Polychromatic418967fa.accept_19_15_13_2_1_6851 15 32 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 135
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 135 (accept_3_4 13 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 135 (accept_3_4 10 32 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 135 (Polychromatic418967fa.accept_25_9_7_10_1_6850 9 32 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 135
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 135 (accept_3_4 7 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  135 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 32 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 135 (accept_3_4 4 32 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 135 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 32 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 135 (Polychromatic418967fa.accept_14_2_4_9_1_2121 2
  32 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 135 (accept_3_4 1 32 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 135)))))))))))))))))))))))))))))))) (allB_succ 31 135
  (allA_succ_of_accept 30 31 135 (Polychromatic418967fa.accept_16_14_15_7_1_5655 30 31 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 135 (accept_3_5 29 31 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 27
  31 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 135 (accept_3_5 26 31
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 135
  (Polychromatic418967fa.accept_17_8_14_16_1_6849 25 31 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 135 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 31 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 135 (accept_3_5 23 31 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 135 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  21 31 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 135 (accept_3_5 20
  31 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 31 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 135 (Polychromatic418967fa.accept_21_18_10_9_1_5297 18 31 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 135 (accept_3_5 17 31 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  31 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 135 (accept_3_5 14 31
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 31 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 31 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 135 (accept_3_5 11 31 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 31 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  31 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 135 (accept_3_5 8 31 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 135 (Polychromatic418967fa.accept_21_7_10_9_1_6848
  7 31 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 31 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 135 (accept_3_5 5 31 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 135 (Polychromatic418967fa.accept_16_3_15_7_1_3417 3 31 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 135 (accept_3_5 2 31 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 31 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 135))))))))))))))))))))))))))))))) (allB_succ 30 135
  (allA_succ_of_accept 29 30 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 135 (Polychromatic418967fa.accept_11_6_8_3_1_2236 28 30 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 135 3 9 10 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 135
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 30 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 30 135 5 5 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 30 135 3 8 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 135 (Polychromatic418967fa.accept_13_10_4_5_1_2331 23 30 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 135 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 30 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 30 135 3 7 10 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 135 5 4 6 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 135
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 30 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 135 3 6 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 135 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 30 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 135 15 1 2 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 135
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 30 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 30 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 135 3 4 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 135 (Polychromatic418967fa.accept_14_11_2_9_1_5873 11 30 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 135 5 2 6 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 135 3 3 10 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 135
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 30 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 135 (Polychromatic418967fa.accept_14_7_2_9_1_2093 7 30 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 135 3 2 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 135 5 1 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 30 135 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 30 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 30 135 3 1 10 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 30 135
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 30 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 135)))))))))))))))))))))))))))))) (allB_succ 29 135 (allA_succ_of_accept
  28 29 135 (accept_3_4 28 29 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 29 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 135 (accept_3_4 25 29 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 135 (Polychromatic418967fa.accept_20_3_9_15_1_6847
  23 29 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 135 (accept_3_4 22
  29 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 135
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 29 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 135 (accept_3_4 19 29 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 17
  29 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 135 (accept_3_4 16 29
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 135
  (Polychromatic418967fa.accept_11_4_7_3_1_289 15 29 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 135 (accept_3_4 13 29 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 135 (Polychromatic418967fa.accept_18_12_11_9_1_4257 12 29 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 135
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 29 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 135 (accept_3_4 10 29 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 135 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 29 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 135 (accept_3_4 7 29 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 135
  (Polychromatic418967fa.accept_19_5_10_2_1_1731 5 29 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 135 (accept_3_4 4 29 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  135 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 29 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 135 (accept_3_4 1 29 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 135))))))))))))))))))))))))))))) (allB_succ 28 135 (allA_succ_of_accept 27 28 135
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 28 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 135 (accept_3_5 26 28 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 135 (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 28 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 135 (accept_3_5 23 28 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 28 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 135
  (Polychromatic418967fa.accept_16_5_12_7_1_3411 21 28 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 135 (accept_3_5 20 28 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 135 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 28 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 135 (accept_3_5 17 28 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 135 (Polychromatic418967fa.accept_13_3_2_5_1_1632 16 28 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 135
  (Polychromatic418967fa.accept_17_15_11_16_1_3263 15 28 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 28 135 (accept_3_5 14 28 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 28 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 28 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 135 (accept_3_5 11 28 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 135 (Polychromatic418967fa.accept_13_10_2_5_1_1633
  10 28 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 135
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 28 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 135 (accept_3_5 8 28 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 135 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 28 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 135 (accept_3_5 5 28 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 135 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 28 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 135 (Polychromatic418967fa.accept_8_3_4_7_1_475 3
  28 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 135 (accept_3_5 2 28 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 135))))))))))))))))))))))))))))
  (allB_succ 27 135 (allA_succ_of_accept 26 27 135 (Polychromatic418967fa.accept_17_9_10_16_1_3217 26 27 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 135
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 27 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 135 3 8 9 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 27 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 27 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 135 3 7 9 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 135
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 27 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 135 (Polychromatic418967fa.accept_11_8_5_3_1_694 19 27 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 135 9 2 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 27 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 135
  (Polychromatic418967fa.accept_13_3_1_5_1_499 16 27 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 135 3 5 9 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 135 (Polychromatic418967fa.accept_19_14_8_2_1_6846 14 27 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 27 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 135 3 4 9 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 135
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 27 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 27 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 135 9 1 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 27 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 135
  (Polychromatic418967fa.accept_17_7_10_16_1_5582 7 27 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 135 3 2 9 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 135 (Polychromatic418967fa.accept_16_5_11_7_1_5635 5 27 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 27 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 135 3 1 9 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 135
  (Polychromatic418967fa.accept_10_2_7_5_1_605 2 27 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 27 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 135))))))))))))))))))))))))))) (allB_succ 26 135 (allA_succ_of_accept 25
  26 135 (accept_3_4 25 26 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 135
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 26 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 135 (accept_3_4 22 26 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 135 (Polychromatic418967fa.accept_19_1_7_2_1_4106
  20 26 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 135 (accept_3_4 19
  26 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 135
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 26 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 135 (accept_3_4 16 26 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 135 (Polychromatic418967fa.accept_21_15_5_9_1_5315 15 26 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 135
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 26 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 135 (accept_3_4 13 26 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  26 135 (Polychromatic418967fa.accept_20_12_6_15_1_6845 12 26 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 135 (accept_3_4 10 26 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 135
  (Polychromatic418967fa.accept_17_8_9_16_1_6844 8 26 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 135 (accept_3_4 7 26 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  135 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 26 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 135 (accept_3_4 4 26 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 26 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 135 (Polychromatic418967fa.accept_23_2_3_20_1_6843
  2 26 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 135 (accept_3_4 1 26
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 135)))))))))))))))))))))))))) (allB_succ 25 135
  (allA_succ_of_accept 24 25 135 (Polychromatic418967fa.accept_16_8_9_7_1_768 24 25 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 135 (accept_3_5 23 25 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 135 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 25 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 135 5 4 5 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 135
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 25 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 135 (accept_3_5 17 25 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 25 135 5 3 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 25 135 (accept_3_5 14 25 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 25 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 135
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 25 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 135 (accept_3_5 11 25 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25
  135 5 2 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25
  135 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 25 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 135 (accept_3_5 8 25 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  135 (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 25 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 25 135 5 1 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 25 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 135
  (Polychromatic418967fa.accept_16_3_9_7_1_6842 3 25 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 135 (accept_3_5 2 25 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  135 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 25 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 25 135))))))))))))))))))))))))) (allB_succ 24 135 (allA_succ_of_accept 23 24 135
  (Polychromatic418967fa.accept_11_1_2_3_1_688 23 24 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 24 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 135 3 7 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 24 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 24 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 24 135 3 6 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 24 135 (Polychromatic418967fa.accept_16_1_8_7_1_3377 17 24 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 135 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 24 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 24 135 3 5 8 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 24 135
  (Polychromatic418967fa.accept_18_14_6_9_1_1950 14 24 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 135 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 24 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 135 3 4 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 135 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 24 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 135
  (Polychromatic418967fa.accept_17_10_7_16_1_6841 10 24 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 24 135 3 3 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 24 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 24 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 135 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 24 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 135 3 2 8 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 135 (Polychromatic418967fa.accept_16_4_8_7_1_3396 4 24 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 135 3 1 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 135 (Polychromatic418967fa.accept_18_2_6_9_1_1032 2 24 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 24 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 135)))))))))))))))))))))))) (allB_succ 23 135 (allA_succ_of_accept 22 23 135 (accept_3_4 22 23 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 135 (Polychromatic418967fa.accept_12_9_11_3_1_772
  21 23 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 135 (accept_3_4 19 23 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 135 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 23 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 135 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 23 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 135 (accept_3_4 16 23 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 135 (Polychromatic418967fa.accept_13_2_10_5_1_1643 15 23 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 135 (accept_3_4 13 23 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 135 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 23 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 135 (Polychromatic418967fa.accept_19_11_4_2_1_1700 11 23 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 135 (accept_3_4 10 23 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 135 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 23 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 135 (accept_3_4 7 23 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  135 (Polychromatic418967fa.accept_13_6_10_5_1_1648 6 23 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 23 135 (Polychromatic418967fa.accept_19_5_4_2_1_6840 5 23 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 135 (accept_3_4 4 23 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 135 (Polychromatic418967fa.accept_21_3_2_9_1_5338 3 23 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 135 (accept_3_4 1 23 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  135))))))))))))))))))))))) (allB_succ 22 135 (allA_succ_of_accept 21 22 135 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 22 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 135 (accept_3_5 20
  22 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22 135
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 22 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 22 135 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 22 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 135 (accept_3_5 17 22 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 22 135 (Polychromatic418967fa.accept_13_3_9_5_1_2340 16 22 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 135 (Polychromatic418967fa.accept_13_2_9_5_1_959
  15 22 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 135 (accept_3_5 14
  22 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 22 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 22 135 (Polychromatic418967fa.accept_18_12_4_9_1_5452 12 22 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 135 (accept_3_5 11 22 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 22 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 22 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 135 (accept_3_5 8 22 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 135
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 22 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 22 135 (accept_3_5 5 22 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22
  135 (Polychromatic418967fa.accept_13_4_9_5_1_1641 4 22 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 22 135 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 22 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 135 (accept_3_5 2 22 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 135)))))))))))))))))))))) (allB_succ 21 135
  (allA_succ_of_accept 20 21 135 (Polychromatic418967fa.accept_17_3_4_16_1_3208 20 21 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 135 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 21 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 135 3 6 7 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 135
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 21 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 135 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 21 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 135 3 5 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 135
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 21 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 135 3 4 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 135 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 21 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 135 3 3 7 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 135
  (Polychromatic418967fa.accept_18_8_3_9_1_4232 8 21 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 135 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 21 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 135 3 2 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 135 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 21 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 135
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 21 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 135 3 1 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 135 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 21 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 135))))))))))))))))))))) (allB_succ 20 135
  (allA_succ_of_accept 19 20 135 (accept_3_4 19 20 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 20 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 135 (accept_3_4 16 20 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 20 135 5 3 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 20 135 (Polychromatic418967fa.accept_16_14_4_7_1_2380 14 20 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 135 (accept_3_4 13 20 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 135 (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 20
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 135
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 135 5 2 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 135 (Polychromatic418967fa.accept_19_9_1_2_1_6839 9 20 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 20 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 135 (accept_3_4 7 20 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 135 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6
  20 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 135 5 1 4 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 135 (accept_3_4 4 20
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 135 (Polychromatic418967fa.accept_7_3_6_2_1_90
  3 20 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 135
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 2 20 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 135 (accept_3_4 1 20 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  135)))))))))))))))))))) (allB_succ 19 135 (allA_succ_of_accept 18 19 135 (Polychromatic418967fa.accept_7_4_5_2_1_243
  18 19 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 135 (accept_3_5 17
  19 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 135
  (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 19 135 (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 19 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 135 (accept_3_5 14 19 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 19 135 (Polychromatic418967fa.accept_25_13_19_10_1_3337 13 19 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 135
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 19 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 135 (accept_3_5 11 19 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 135 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 19 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 135 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 19 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 135 (accept_3_5 8 19 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 135 (Polychromatic418967fa.accept_14_7_5_9_1_2911 7 19 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 135
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 19 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 135 (accept_3_5 5 19 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 19 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 135 (accept_3_5 2 19 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 135 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 19 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 135))))))))))))))))))) (allB_succ 18 135 (allA_succ_of_accept 17
  18 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 135 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 18 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 135 3 5 6 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 135 (Polychromatic418967fa.accept_12_2_6_3_1_331 14
  18 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 135 3 4 6 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 135 (Polychromatic418967fa.accept_16_11_2_7_1_3374 11 18 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 135 (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 18
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 135 9 1 2 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 135
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 18 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 135 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 18 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 135 3 2 6 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 135
  (Polychromatic418967fa.accept_11_4_7_3_1_289 4 18 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 135 3 1 6 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 18 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 135)))))))))))))))))) (allB_succ 17 135
  (allA_succ_of_accept 16 17 135 (accept_3_4 16 17 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 135 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 17 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 135 (accept_3_4 13 17 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 135 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 135
  (Polychromatic418967fa.accept_25_11_17_10_1_6838 11 17 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 17 135 (accept_3_4 10 17 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 17 135 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 17 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 135 (accept_3_4 7 17 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 135
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 135 (accept_3_4 4 17 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  135 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 17 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 135 (accept_3_4 1 17 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 135))))))))))))))))) (allB_succ 16 135 (allA_succ_of_accept 15 16 135
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 16 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 135 (accept_3_5 14 16 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 135 (Polychromatic418967fa.accept_18_12_16_9_1_4198 12 16 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 135 (accept_3_5 11 16 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 135 (Polychromatic418967fa.accept_20_10_16_15_1_1536 10 16
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 135
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 16 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 135 (accept_3_5 8 16 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 135 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 16 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 135 (accept_3_5 5 16 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 135 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 16 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 135 (Polychromatic418967fa.accept_19_3_16_2_1_6837
  3 16 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 135 (accept_3_5 2 16
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 135 (Polychromatic418967fa.accept_6_1_4_3_1_14
  1 16 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 135)))))))))))))))) (allB_succ 15
  135 (allA_succ_of_accept 14 15 135 (Polychromatic418967fa.accept_16_14_15_7_1_5655 14 15 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  15 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 135 3 4 5 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 135
  (Polychromatic418967fa.accept_16_11_15_7_1_5654 11 15 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 15 135 5 2 3 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 15 135 3 3 5 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 135 (Polychromatic418967fa.accept_14_8_1_9_1_2085 8 15 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 135 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 15 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 135 3 2 5 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 15 135 5 1 3 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 135
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 15 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 15 135 3 1 5 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 15 135 (Polychromatic418967fa.accept_21_2_15_9_1_3838 2 15 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 135 (Polychromatic418967fa.accept_17_1_15_16_1_2202 1 15 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 135))))))))))))))) (allB_succ 14 135
  (allA_succ_of_accept 13 14 135 (accept_3_4 13 14 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  14 135 (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 14 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 14 135 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 135 (accept_3_4 10 14 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 135
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 8 14 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 14 135 (accept_3_4 7 14 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14
  135 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 14 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 14 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 135 (accept_3_4 4 14 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 14 135 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 14 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 135 (Polychromatic418967fa.accept_17_2_14_16_1_2187
  2 14 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 135 (accept_3_4 1 14
  135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 135)))))))))))))) (allB_succ 13 135 (allA_succ_of_accept 12
  13 135 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 13 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 135 (accept_3_5 11 13 135 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 135 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 13 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 135 (accept_3_5 8 13 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 135 (Polychromatic418967fa.accept_10_7_3_5_1_301 7
  13 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 135
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 135 (accept_3_5 5 13 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  135 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 135 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 13 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 135 (accept_3_5 2 13 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 135 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 13 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 135))))))))))))) (allB_succ 12 135 (allA_succ_of_accept 11 12
  135 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 12 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 135 3 3 4 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 135 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 12 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 135
  (Polychromatic418967fa.accept_10_7_2_5_1_298 7 12 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 135 3 2 4 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 135 (Polychromatic418967fa.accept_16_5_12_7_1_3411 5 12 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 135 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 12 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 135 3 1 4 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 135
  (Polychromatic418967fa.accept_11_2_1_3_1_683 2 12 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 135 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 12 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 135)))))))))))) (allB_succ 11 135 (allA_succ_of_accept 10 11 135
  (accept_3_4 10 11 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 135
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 11 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 135 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 135 (accept_3_4 7 11 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 135 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 11 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 135 (Polychromatic418967fa.accept_7_5_4_2_1_235 5
  11 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 135 (accept_3_4 4 11 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 135 (Polychromatic418967fa.accept_13_3_11_5_1_2348
  3 11 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 135
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 135 (accept_3_4 1 11 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  135))))))))))) (allB_succ 10 135 (allA_succ_of_accept 9 10 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 135 (accept_3_5 8 10 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 135 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 135
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 10 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 10 135 5 1 2 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 10 135 (Polychromatic418967fa.accept_13_4_10_5_1_1644 4 10 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 135 (Polychromatic418967fa.accept_16_3_10_7_1_4518 3 10 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 135 (accept_3_5 2 10 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 135 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 135)))))))))) (allB_succ 9 135
  (allA_succ_of_accept 8 9 135 (Polychromatic418967fa.accept_16_8_9_7_1_768 8 9 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 135 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 9 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 135 3 2 3 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 135
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 9 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 135 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 9 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 135 3 1 3 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 135
  (Polychromatic418967fa.accept_10_1_9_5_1_83 1 9 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 135))))))))) (allB_succ 8 135 (allA_succ_of_accept 7 8 135 (accept_3_4 7 8 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 135 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 8 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 135
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 135 (accept_3_4 4 8 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 135
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 8 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 135 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 8 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 135 (accept_3_4 1 8 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 135)))))))) (allB_succ 7 135 (allA_succ_of_accept 6 7 135
  (Polychromatic418967fa.accept_17_6_7_16_1_6836 6 7 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 135 (accept_3_5 5 7 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 135
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 135 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 7 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 135 (accept_3_5 2 7 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 135 (Polychromatic418967fa.accept_19_1_7_2_1_4106 1 7 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 135))))))) (allB_succ 6 135 (allA_succ_of_accept 5 6 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 135 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 6 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 135 3 1 2 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 135 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 6 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 135
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 135)))))) (allB_succ 5 135 (allA_succ_of_accept 4 5 135 (accept_3_4 4 5 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 135 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 5 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 135 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 135 (accept_3_4 1 5 135
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 135))))) (allB_succ 4 135 (allA_succ_of_accept 3 4 135
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 4 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 135 (accept_3_5 2 4 135 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 135
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 135)))) (allB_succ 3 135 (allA_succ_of_accept 2 3 135 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 3 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 135
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 3 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 135))) (allB_succ 2 135 (allA_succ_of_accept 1 2 135 (accept_3_4 1 2 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 135)) (allB_two
  135)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


