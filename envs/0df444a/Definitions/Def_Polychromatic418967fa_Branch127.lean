-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch127
-- name    : Polychromatic418967fa_Branch127
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:12:25.337643+00:00
-- url     : https://prove2.me/theorems/1d7cfa33-049e-45a5-aa30-6ef50bdc200d
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

def Polychromatic418967fa.branch_127 : allB 127 127 :=
  allB_succ' 2 126 127 (Eq.refl Bool.true) (allA_succ_of_accept 1 126 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  126 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 127)) (allB_succ' 3 125 127
  (Eq.refl Bool.true) (allA_of_3_1 3 125 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 124 127 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 124 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 127 (accept_3_3 2 124 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 124 127 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 124 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 127)))) (allB_succ' 5 123 127 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 123 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 123 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 127 (accept_3_3 2 123 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 127 (Polychromatic418967fa.accept_16_1_11_15_1_498
  1 123 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 127))))) (allB_succ' 6 122 127
  (Eq.refl Bool.true) (allA_of_3_1 6 122 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 121 127 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 121 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 127 (accept_3_3 5 121 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 127 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 121 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 127
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 121 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 127 (accept_3_3 2 121 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 127 (Polychromatic418967fa.accept_13_1_4_10_1_622 1 121 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 127))))))) (allB_succ' 8 120 127 (Eq.refl Bool.true) (allA_succ_of_accept 7 120 127
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 120 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 120 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 120 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 127 (accept_3_3 5 120 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 120 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 120 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 127 (Polychromatic418967fa.accept_18_3_12_1_1_3787
  3 120 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 127 (accept_3_3 2
  120 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 127
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 1 120 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 127)))))))) (allB_succ' 9 119 127 (Eq.refl Bool.true) (allA_of_3_1 9 119 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 10 118 127 (Eq.refl Bool.true) (allA_succ_of_accept 9 118 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 118 127 (accept_3_3 8 118 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  118 127 (Polychromatic418967fa.accept_14_7_6_1_1_1656 7 118 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 118 127 (Polychromatic418967fa.accept_15_6_13_7_1_222 6 118 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 127 (accept_3_3 5 118 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 118 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 118 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 118 127 (accept_3_3 2 118 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  118 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 118 127)))))))))) (allB_succ' 11 117 127 (Eq.refl Bool.true) (allA_succ_of_accept 10 117 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 117 127 (Polychromatic418967fa.accept_19_9_3_13_1_2300 9 117 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 127 (accept_3_3 8 117 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 117 127 (Polychromatic418967fa.accept_19_7_3_13_1_3492 7 117 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 127 (accept_3_3 5 117 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 117 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 127 (accept_3_3 2 117 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 127 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 117 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117 127))))))))))) (allB_succ' 12 116 127 (Eq.refl
  Bool.true) (allA_of_3_1 12 116 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 115 127 (Eq.refl Bool.true)
  (allA_succ_of_accept 12 115 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 115 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 127 (accept_3_3 11 115 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 115 127 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 115 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 127
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 127 (accept_3_3 8 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 127 (Polychromatic418967fa.accept_16_7_3_15_1_2940 7 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 115 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 127 (accept_3_3 5 115 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 115 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 127
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 127 (accept_3_3 2 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 127 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 127))))))))))))) (allB_succ' 14 114 127 (Eq.refl Bool.true) (allA_succ_of_accept 13 114 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 114 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 114 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 127 (accept_3_3 11 114 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 114 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 114 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  114 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 127 (accept_3_3 8 114
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 127
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 114 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 114 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 114 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 127 (accept_3_3 5 114 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 114 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 114 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  114 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 127 (accept_3_3 2 114
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 127 (Polychromatic418967fa.accept_4_1_2_3_1_9
  1 114 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 127)))))))))))))) (allB_succ' 15
  113 127 (Eq.refl Bool.true) (allA_of_3_1 15 113 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 112 127
  (Eq.refl Bool.true) (allA_succ_of_accept 15 112 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 127 (accept_3_3 14 112 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 112 127 (Polychromatic418967fa.accept_24_13_16_7_1_1542 13 112
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 127
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 112 127 (accept_3_3 11 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 112 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 112 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 127 (accept_3_3 8 112 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 112 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 112 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 127 (accept_3_3 5 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 127 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 127 (accept_3_3 2 112 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 127 (Polychromatic418967fa.accept_22_1_2_17_1_6348 1 112 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 127)))))))))))))))) (allB_succ' 17 111 127 (Eq.refl
  Bool.true) (allA_succ_of_accept 16 111 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 127 (Polychromatic418967fa.accept_9_6_3_1_1_155
  15 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 127 (accept_3_3 14
  111 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 127
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 111 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 111 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 127 (accept_3_3 11 111 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 111 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 111 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 9
  111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 127 (accept_3_3 8 111
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 127
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 111 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 111 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 127 (accept_3_3 5 111 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 111 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 127 (Polychromatic418967fa.accept_13_3_7_10_1_668
  3 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 127 (accept_3_3 2
  111 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 127
  (Polychromatic418967fa.accept_15_1_6_7_1_6282 1 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111 127))))))))))))))))) (allB_succ' 18 110 127 (Eq.refl Bool.true) (allA_of_3_1 18 110 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 109 127 (Eq.refl Bool.true) (allA_succ_of_accept 18 109 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 127 (accept_3_3 17 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 127 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 127 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 109 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 127 (accept_3_3 14 109 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 127 (Polychromatic418967fa.accept_21_13_4_1_1_942 13 109
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 127
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 127 (accept_3_3 11 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 127 (Polychromatic418967fa.accept_27_9_1_19_1_4355 9 109 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 127 (accept_3_3 8 109 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 127 (Polychromatic418967fa.accept_21_7_4_1_1_3300 7 109 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 127 (accept_3_3 5 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 127 (Polychromatic418967fa.accept_13_4_5_10_1_1247 4 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 109 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 127 (accept_3_3 2 109 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 127 (Polychromatic418967fa.accept_17_1_7_8_1_6347 1 109 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109 127))))))))))))))))))) (allB_succ' 20 108 127
  (Eq.refl Bool.true) (allA_succ_of_accept 19 108 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 108 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 127
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 108 127 (accept_3_3 17 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 108 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 108 127 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 108 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 127 (accept_3_3 14 108 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 127 (Polychromatic418967fa.accept_16_13_12_15_1_6290 13
  108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 127
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 108 127 (accept_3_3 11 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 108 127 (Polychromatic418967fa.accept_15_10_3_7_1_715 10 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 108 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 108 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 127 (accept_3_3 8 108 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 127 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 108 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 127
  (Polychromatic418967fa.accept_13_6_4_10_1_660 6 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 108 127 (accept_3_3 5 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  108 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 108 127 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 108 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 127 (accept_3_3 2 108 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 127 (Polychromatic418967fa.accept_13_1_4_10_1_622 1 108 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108 127)))))))))))))))))))) (allB_succ' 21 107 127
  (Eq.refl Bool.true) (allA_of_3_1 21 107 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 106 127 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 127 (accept_3_3 20 106 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 127 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 106 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 127
  (Polychromatic418967fa.accept_13_5_2_10_1_248 18 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 127 (accept_3_3 17 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 106 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 127 (accept_3_3 14 106 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 127
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 127 (accept_3_3 11 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 127 (Polychromatic418967fa.accept_15_10_1_7_1_5207 10 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 127 (accept_3_3 8 106 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 127 (Polychromatic418967fa.accept_14_7_8_1_1_1621 7 106 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 127 (accept_3_3 5 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 106 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 127 (accept_3_3 2 106 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 127)))))))))))))))))))))) (allB_succ' 23 105 127
  (Eq.refl Bool.true) (allA_succ_of_accept 22 105 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 105 127 (accept_3_3 20 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 105 127 (Polychromatic418967fa.accept_31_19_12_3_1_6346 19 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 105 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 127 (accept_3_3 17 105 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 127
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 105 127 (accept_3_3 14 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 105 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 105 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 105 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 127 (accept_3_3 11 105 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 127
  (Polychromatic418967fa.accept_13_9_1_10_1_647 9 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 127 (accept_3_3 8 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  105 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 127 (accept_3_3 5 105 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 127 (accept_3_3 2 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 127 (Polychromatic418967fa.accept_19_1_10_13_1_4880 1 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105 127))))))))))))))))))))))) (allB_succ' 24 104 127 (Eq.refl Bool.true) (allA_of_3_1 24 104
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 103 127 (Eq.refl Bool.true) (allA_succ_of_accept 24 103
  127 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 127 (accept_3_3 23 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 127 (Polychromatic418967fa.accept_13_9_12_10_1_242 22 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 103 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 127 (accept_3_3 20 103 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 127 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 103 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 127
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 127 (accept_3_3 17 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 127 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 103 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 127 (accept_3_3 14 103 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 103 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 127
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 127 (accept_3_3 11 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 127 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 103 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 127 (accept_3_3 8 103 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 103 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 127
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 127 (accept_3_3 5 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 127 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 103 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 127 (accept_3_3 2 103 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 127 (Polychromatic418967fa.accept_19_1_8_13_1_4875 1 103 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 127))))))))))))))))))))))))) (allB_succ' 26 102 127
  (Eq.refl Bool.true) (allA_succ_of_accept 25 102 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 127
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 127 (accept_3_3 23 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 127 (accept_3_3 20 102 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 102 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 127
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 102 127 (accept_3_3 17 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 102 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 102 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 102 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 127 (accept_3_3 14 102 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 127
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 102 127 (accept_3_3 11 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 102 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 102 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 127 (accept_3_3 8 102 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 102 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 127
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 127 (accept_3_3 5 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 102 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 102 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 127 (accept_3_3 2 102 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 127)))))))))))))))))))))))))) (allB_succ' 27 101 127
  (Eq.refl Bool.true) (allA_of_3_1 27 101 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 100 127 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 100 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 100 127 (accept_3_3 26 100 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 100 127 (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 100 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 100 127
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 100 127 (accept_3_3 23 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 100 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 100 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 100 127 (accept_3_3 20 100 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 100 127 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 100 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 100 127
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 100 127 (accept_3_3 17 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 100 127 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 100 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 100 127 (accept_3_3 14 100 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 100 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 127
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 100 127 (accept_3_3 11 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 100 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 100 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 127 (accept_3_3 8 100 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 100 127 (Polychromatic418967fa.accept_11_7_1_6_1_1281
  7 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 127
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 100 127 (accept_3_3 5 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  100 127 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 100 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 100 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 127 (accept_3_3 2 100 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 127 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 100 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 127)))))))))))))))))))))))))))) (allB_succ' 29 99
  127 (Eq.refl Bool.true) (allA_succ_of_accept 28 99 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 127
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 127 (accept_3_3 26 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 127 (Polychromatic418967fa.accept_13_12_8_10_1_1879 25 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 127 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 99 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 127 (accept_3_3 23 99 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 99 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 127
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 127 (accept_3_3 20 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 127 (Polychromatic418967fa.accept_21_19_15_1_1_6345 19 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 127 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 99 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 127 (accept_3_3 17 99 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 127
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 127 (accept_3_3 14 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 127 (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 127 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 99 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 127 (accept_3_3 11 99 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 99 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 127
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 127 (accept_3_3 8 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  127 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 127 (Polychromatic418967fa.accept_17_6_14_8_1_3858 6 99 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 127 (accept_3_3 5 99 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 127
  (Polychromatic418967fa.accept_18_3_9_1_1_3690 3 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 127 (accept_3_3 2 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  127 (Polychromatic418967fa.accept_15_1_9_7_1_3130 1 99 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 127))))))))))))))))))))))))))))) (allB_succ' 30 98 127 (Eq.refl Bool.true) (allA_of_3_1 30 98
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 97 127 (Eq.refl Bool.true) (allA_succ_of_accept 30 97 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 127 (accept_3_3 29 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 127 (Polychromatic418967fa.accept_13_2_6_10_1_2703 28 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 127 (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 97 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 127 (accept_3_3 26 97 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 127 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 97 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 127 (accept_3_3 23 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 127 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 97 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 127 (accept_3_3 20 97 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 97 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 127 (accept_3_3 17 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 97 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 127 (accept_3_3 14 97 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 97 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 127
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 127 (accept_3_3 11 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 97 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 127 (accept_3_3 8 97 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 127 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 97 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 127 (accept_3_3 5 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  127 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 97 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 127 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 97 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 127 (accept_3_3 2 97 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 127 (Polychromatic418967fa.accept_19_1_2_13_1_4934 1 97 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 127))))))))))))))))))))))))))))))) (allB_succ' 32 96 127
  (Eq.refl Bool.true) (allA_succ_of_accept 31 96 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 96 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 127 (accept_3_3 29 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 127 (Polychromatic418967fa.accept_13_2_5_10_1_250 28 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 96 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 127 (accept_3_3 26 96 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 127 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 96 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 127
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 127 (accept_3_3 23 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 96 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 127 (accept_3_3 20 96 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 127 (Polychromatic418967fa.accept_13_6_5_10_1_1213 19 96 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 127
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 127 (accept_3_3 17 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 127 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 96 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 127 (accept_3_3 14 96 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 96 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 127 (accept_3_3 11 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 127 (Polychromatic418967fa.accept_17_9_11_8_1_5077 9 96 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 127 (accept_3_3 8 96 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 127
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 127 (accept_3_3 5 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  127 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 96 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 96 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 127 (accept_3_3 2 96 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 127 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 96 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 127)))))))))))))))))))))))))))))))) (allB_succ' 33 95 127
  (Eq.refl Bool.true) (allA_of_3_1 33 95 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 94 127 (Eq.refl
  Bool.true) (allA_succ_of_accept 33 94 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 127 (accept_3_3 32 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 127 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 94 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 127
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 127 (accept_3_3 29 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 127 (accept_3_3 26 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 127 (accept_3_3 23 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 127 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 127 (accept_3_3 20 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 94 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 127
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 127 (accept_3_3 17 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 127 (accept_3_3 14 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 127
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 127 (accept_3_3 11 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 127 (Polychromatic418967fa.accept_15_10_4_7_1_3127 10 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 127 (accept_3_3 8 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 94 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 127 (accept_3_3 5 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  127 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 94 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 94 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 94 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 127 (accept_3_3 2 94 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 94 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 127)))))))))))))))))))))))))))))))))) (allB_succ' 35 93 127
  (Eq.refl Bool.true) (allA_succ_of_accept 34 93 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 127
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 127 (accept_3_3 32 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 127 (accept_3_3 29 93 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 127
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 127 (accept_3_3 26 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 93 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 127 (accept_3_3 23 93 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 127
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 127 (accept_3_3 20 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 127 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 127 (accept_3_3 17 93 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 127
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 127 (accept_3_3 14 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 127 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 93 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 127 (accept_3_3 11 93 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 127
  (Polychromatic418967fa.accept_18_9_3_1_1_2559 9 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 127 (accept_3_3 8 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  127 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 127 (accept_3_3 5 93 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 127 (accept_3_3 2 93 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 127 (Polychromatic418967fa.accept_11_1_5_6_1_397 1
  93 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  127))))))))))))))))))))))))))))))))))) (allB_succ' 36 92 127 (Eq.refl Bool.true) (allA_of_3_1 36 92 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 91 127 (Eq.refl Bool.true) (allA_succ_of_accept 36 91 127
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 127 (accept_3_3 35 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 127 (Polychromatic418967fa.accept_10_4_1_7_1_371 34 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 127 (Polychromatic418967fa.accept_16_1_11_15_1_498 33 91 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 127 (accept_3_3 32 91 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 127 (Polychromatic418967fa.accept_11_9_3_6_1_797 31 91 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 127
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 127 (accept_3_3 29 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 127 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 127 (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 91 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 127 (accept_3_3 26 91 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 127 (Polychromatic418967fa.accept_15_10_1_7_1_5207 25 91
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 127
  (Polychromatic418967fa.accept_10_4_1_7_1_371 24 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 127 (accept_3_3 23 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 127 (Polychromatic418967fa.accept_14_8_7_1_1_1615 22 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 127 (Polychromatic418967fa.accept_15_6_1_7_1_4079 21 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 127 (accept_3_3 20 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 127 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 91 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 127
  (Polychromatic418967fa.accept_20_18_11_7_1_6344 18 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 127 (accept_3_3 17 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 127 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 127 (Polychromatic418967fa.accept_17_15_6_8_1_6343 15 91 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 127 (accept_3_3 14 91 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 127 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 91
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 127
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 127 (accept_3_3 11 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 127 (Polychromatic418967fa.accept_15_10_1_7_1_5207 10 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 127 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 127 (accept_3_3 8 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 127 (Polychromatic418967fa.accept_16_7_11_15_1_2929 7 91 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 127
  (Polychromatic418967fa.accept_10_6_1_7_1_342 6 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 127 (accept_3_3 5 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  127 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 91 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 127 (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 91 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 127 (accept_3_3 2 91 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 127 (Polychromatic418967fa.accept_16_1_11_15_1_498 1 91 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 127))))))))))))))))))))))))))))))))))))) (allB_succ' 38 90 127
  (Eq.refl Bool.true) (allA_succ_of_accept 37 90 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 127
  (Polychromatic418967fa.accept_21_15_6_1_1_6306 36 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 90 127 (accept_3_3 35 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  90 127 (Polychromatic418967fa.accept_13_8_12_10_1_4414 34 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 90 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 127 (accept_3_3 32 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 127 (Polychromatic418967fa.accept_19_12_14_13_1_6342 31 90 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 127
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 127 (accept_3_3 29 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  90 127 (Polychromatic418967fa.accept_13_2_12_10_1_2649 28 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 127 (Polychromatic418967fa.accept_16_11_10_15_1_6301 27 90 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 127 (accept_3_3 26 90 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 127
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 90 127 (accept_3_3 23 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 127 (Polychromatic418967fa.accept_13_9_12_10_1_242 22 90 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 127 (accept_3_3 20 90 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 19
  90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 127
  (Polychromatic418967fa.accept_19_18_14_13_1_6341 18 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 90 127 (accept_3_3 17 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 90 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 127 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 90 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 127 (accept_3_3 14 90 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 127
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 127 (accept_3_3 11 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  90 127 (Polychromatic418967fa.accept_23_10_21_12_1_6340 10 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 90 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 127 (accept_3_3 8 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 127 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 90 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 127
  (Polychromatic418967fa.accept_13_6_12_10_1_690 6 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 127 (accept_3_3 5 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  127 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 90 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 90 127 (Polychromatic418967fa.accept_17_3_5_8_1_1687 3 90 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 127 (accept_3_3 2 90 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 90 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 127)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 89 127
  (Eq.refl Bool.true) (allA_of_3_1 39 89 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 88 127 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 88 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 127 (accept_3_3 38 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 127 (Polychromatic418967fa.accept_19_18_12_13_1_2311 37 88 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 127
  (Polychromatic418967fa.accept_15_6_13_7_1_222 36 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 127 (accept_3_3 35 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 127 (accept_3_3 32 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 88 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 127
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 127 (accept_3_3 29 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 127 (Polychromatic418967fa.accept_16_12_8_15_1_5119 28 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 127 (accept_3_3 26 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 127 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 88 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 127
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 127 (accept_3_3 23 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 127 (accept_3_3 20 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 88 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 127
  (Polychromatic418967fa.accept_19_18_12_13_1_2311 18 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 88 127 (accept_3_3 17 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 88 127 (Polychromatic418967fa.accept_19_16_12_13_1_4843 16 88 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 127 (accept_3_3 14 88 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 127
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 127 (accept_3_3 11 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 127 (accept_3_3 8 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 127 (Polychromatic418967fa.accept_16_7_8_15_1_6327 7 88 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 127 (accept_3_3 5 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  127 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 88 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 127 (accept_3_3 2 88 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 127 (Polychromatic418967fa.accept_16_1_8_15_1_1945 1 88 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 127)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 87
  127 (Eq.refl Bool.true) (allA_succ_of_accept 40 87 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 127
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 127 (accept_3_3 38 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 127 (Polychromatic418967fa.accept_15_6_12_7_1_1360 36 87 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 127 (accept_3_3 35 87 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 87 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 127
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 127 (accept_3_3 32 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 87 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 127 (accept_3_3 29 87 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 127
  (Polychromatic418967fa.accept_11_5_10_6_1_793 27 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 127 (accept_3_3 26 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 127 (Polychromatic418967fa.accept_16_8_7_15_1_6339 24 87 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 127 (accept_3_3 23 87 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 87 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 127 (accept_3_3 20 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 87 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 127 (accept_3_3 17 87 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 127
  (Polychromatic418967fa.accept_21_15_3_1_1_6338 15 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 127 (accept_3_3 14 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 87 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 127 (accept_3_3 11 87 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 87 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 127
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 127 (accept_3_3 8 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  127 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 127 (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 87 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 127 (accept_3_3 5 87 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 87
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 127 (accept_3_3 2 87 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 127 (Polychromatic418967fa.accept_13_1_9_10_1_625 1
  87 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  127))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 86 127 (Eq.refl Bool.true) (allA_of_3_1 42 86 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 85 127 (Eq.refl Bool.true) (allA_succ_of_accept 42 85 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 127 (accept_3_3 41 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 127 (Polychromatic418967fa.accept_24_16_13_7_1_6337 40 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 127 (accept_3_3 38 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 127 (Polychromatic418967fa.accept_19_18_9_13_1_3496 37 85 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 127
  (Polychromatic418967fa.accept_11_3_8_6_1_788 36 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 127 (accept_3_3 35 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 127 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 127 (accept_3_3 32 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 127 (Polychromatic418967fa.accept_15_1_10_7_1_4087 31 85 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 127 (accept_3_3 29 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 127 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 127 (Polychromatic418967fa.accept_15_12_10_7_1_1357 27 85 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 127 (accept_3_3 26 85 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 85 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 127 (accept_3_3 23 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 127 (accept_3_3 20 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 127 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 85 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 127 (accept_3_3 17 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 127 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 127 (accept_3_3 14 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 127 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 85 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 127
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 127 (accept_3_3 11 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 127 (Polychromatic418967fa.accept_20_9_5_7_1_6336 9 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 127 (accept_3_3 8 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 85 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 127 (accept_3_3 5 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  127 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 85 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 127 (accept_3_3 2 85 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 127 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 85 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 127)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 84 127 (Eq.refl Bool.true) (allA_succ_of_accept 43 84 127 (Polychromatic418967fa.accept_8_3_4_7_1_475
  43 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 127
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 127 (accept_3_3 41 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 127 (Polychromatic418967fa.accept_18_3_12_1_1_3787 39 84 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 127 (accept_3_3 38 84 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 127 (Polychromatic418967fa.accept_16_5_4_15_1_1102 37 84
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 127
  (Polychromatic418967fa.accept_17_2_16_8_1_3881 36 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 84 127 (accept_3_3 35 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  84 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 84 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 127 (accept_3_3 32 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 84 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 127
  (Polychromatic418967fa.accept_13_4_6_10_1_1199 30 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 127 (accept_3_3 29 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 127 (Polychromatic418967fa.accept_13_2_6_10_1_2703 28 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 127 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 127 (accept_3_3 26 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 84 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 127
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 127 (accept_3_3 23 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 127 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 127 (accept_3_3 20 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 127 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 84 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 127
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 127 (accept_3_3 17 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 127 (accept_3_3 14 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 84 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 127
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 127 (accept_3_3 11 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 127 (Polychromatic418967fa.accept_22_10_18_17_1_1830 10 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 127 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 127 (accept_3_3 8 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 84 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 127
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 127 (accept_3_3 5 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  127 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 84 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 84 127 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 84 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 127 (accept_3_3 2 84 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 84 127 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 84 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 127)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  83 127 (Eq.refl Bool.true) (allA_of_3_1 45 83 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 82 127
  (Eq.refl Bool.true) (allA_succ_of_accept 45 82 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 127 (accept_3_3 44 82 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 127 (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 82
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 127
  (Polychromatic418967fa.accept_19_4_6_13_1_6335 42 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 127 (accept_3_3 41 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 127 (accept_3_3 38 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 127
  (Polychromatic418967fa.accept_19_17_6_13_1_6334 36 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 127 (accept_3_3 35 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 127 (accept_3_3 32 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 82 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 127
  (Polychromatic418967fa.accept_19_11_6_13_1_3477 30 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 127 (accept_3_3 29 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 127 (accept_3_3 26 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 127
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 127 (accept_3_3 23 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 127 (Polychromatic418967fa.accept_23_22_13_12_1_6297 22 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 127 (accept_3_3 20 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 127 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 82 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 127
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 127 (accept_3_3 17 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 127 (accept_3_3 14 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 127
  (Polychromatic418967fa.accept_11_1_5_6_1_397 12 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 127 (accept_3_3 11 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 127 (accept_3_3 8 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 127 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 82 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 127
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 127 (accept_3_3 5 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  127 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 82 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 82 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 127 (accept_3_3 2 82 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 127)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47
  81 127 (Eq.refl Bool.true) (allA_succ_of_accept 46 81 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 127
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 127 (accept_3_3 44 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 127 (Polychromatic418967fa.accept_15_13_6_7_1_1369 43 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 127 (accept_3_3 41 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 127
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 127 (accept_3_3 38 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 127 (Polychromatic418967fa.accept_13_11_3_10_1_4374 37 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 127 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 127 (accept_3_3 35 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 127
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 127 (accept_3_3 32 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 127 (accept_3_3 29 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 127
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 127 (accept_3_3 26 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 127 (Polychromatic418967fa.accept_21_4_18_1_1_6333 25 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 127 (accept_3_3 23 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 127
  (Polychromatic418967fa.accept_16_5_1_15_1_3922 21 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 127 (accept_3_3 20 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 127 (accept_3_3 17 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 127
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 127 (accept_3_3 14 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 127 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 127 (accept_3_3 11 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 127
  (Polychromatic418967fa.accept_19_9_5_13_1_4867 9 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 127 (accept_3_3 8 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  127 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 127 (accept_3_3 5 81 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 127
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 127 (accept_3_3 2 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  127 (Polychromatic418967fa.accept_15_1_6_7_1_6282 1 81 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 127))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 80 127 (Eq.refl Bool.true)
  (allA_of_3_1 48 80 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 79 127 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 79 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 127 (accept_3_3 47 79 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 79 127 (Polychromatic418967fa.accept_19_8_3_13_1_4863 46 79 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 127
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 127 (accept_3_3 44 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 127 (Polychromatic418967fa.accept_13_4_1_10_1_693 43 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 127 (accept_3_3 41 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 79 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 127
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 127 (accept_3_3 38 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 127 (Polychromatic418967fa.accept_11_4_2_6_1_389 37 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 127 (Polychromatic418967fa.accept_14_8_9_1_1_3313 36 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 127 (accept_3_3 35 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 79 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 127 (accept_3_3 32 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 127 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 127 (accept_3_3 29 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 127 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 79 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 127
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 127 (accept_3_3 26 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 127 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 127 (accept_3_3 23 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 79 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 127
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 127 (accept_3_3 20 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 127 (Polychromatic418967fa.accept_17_2_11_8_1_2726 19 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 127 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 127 (accept_3_3 17 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 127 (Polychromatic418967fa.accept_18_16_7_1_1_6332 16 79 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 127 (accept_3_3 14 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 127 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 127 (accept_3_3 11 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 79 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 127
  (Polychromatic418967fa.accept_13_9_1_10_1_647 9 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 127 (accept_3_3 8 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  127 (Polychromatic418967fa.accept_19_7_3_13_1_3492 7 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 127 (accept_3_3 5 79 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 79 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 127
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 127 (accept_3_3 2 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  127 (Polychromatic418967fa.accept_17_1_11_8_1_2725 1 79 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 79 127))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 78 127 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 78 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 48
  78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 127 (accept_3_3 47 78
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 127
  (Polychromatic418967fa.accept_17_12_10_8_1_5039 46 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 78 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 127 (accept_3_3 44 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 78 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 127 (Polychromatic418967fa.accept_15_12_3_7_1_4123
  42 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 127 (accept_3_3 41
  78 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 127
  (Polychromatic418967fa.accept_9_4_6_1_1_393 40 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 78 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 127 (accept_3_3 38 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 78 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 127
  (Polychromatic418967fa.accept_16_4_14_15_1_6331 36 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 127 (accept_3_3 35 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 127 (accept_3_3 32 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 78 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 127 (accept_3_3 29 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 127 (Polychromatic418967fa.accept_21_7_15_1_1_6330 28 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 127 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 127 (accept_3_3 26 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 127
  (Polychromatic418967fa.accept_21_3_15_1_1_2046 24 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 127 (accept_3_3 23 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 127 (accept_3_3 20 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 127 (Polychromatic418967fa.accept_10_9_8_7_1_714 19 78 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 127
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 127 (accept_3_3 17 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 127 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 127 (accept_3_3 14 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 127 (accept_3_3 11 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 127 (Polychromatic418967fa.accept_15_10_3_7_1_715 10 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 127 (accept_3_3 8 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 78 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 127
  (Polychromatic418967fa.accept_19_6_2_13_1_4945 6 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 127 (accept_3_3 5 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  127 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 78 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 127 (accept_3_3 2 78 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 127))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 77 127 (Eq.refl Bool.true) (allA_of_3_1 51 77 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  52 76 127 (Eq.refl Bool.true) (allA_succ_of_accept 51 76 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 127 (accept_3_3 50 76 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 127 (Polychromatic418967fa.accept_11_5_10_6_1_793
  49 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 127
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 127 (accept_3_3 47 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 127 (accept_3_3 44 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 127 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 76 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 127 (accept_3_3 41 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 127 (accept_3_3 38 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 76 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 127
  (Polychromatic418967fa.accept_15_6_1_7_1_4079 36 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 127 (accept_3_3 35 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 127 (accept_3_3 32 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 127 (Polychromatic418967fa.accept_10_1_6_7_1_710 31 76 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 127
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 127 (accept_3_3 29 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 127 (Polychromatic418967fa.accept_13_2_11_10_1_1881 28 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 127 (accept_3_3 26 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 76 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 127 (accept_3_3 23 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 127 (accept_3_3 20 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 76 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 127
  (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 127 (accept_3_3 17 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 127 (accept_3_3 14 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 127 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 76 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 127
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 127 (accept_3_3 11 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 127 (accept_3_3 8 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 76 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 127 (accept_3_3 5 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  127 (Polychromatic418967fa.accept_13_4_11_10_1_1226 4 76 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 76 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 127 (accept_3_3 2 76 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 127 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 76 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  127)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 75 127 (Eq.refl Bool.true) (allA_succ_of_accept
  52 75 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 127 (accept_3_3 50 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 75 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 127
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 127 (accept_3_3 47 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  75 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 127 (accept_3_3 44 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 75 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 127
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 127 (accept_3_3 41 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 127 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 127 (accept_3_3 38 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 127 (Polychromatic418967fa.accept_28_9_19_15_1_6329 37 75 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 127
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 127 (accept_3_3 35 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 127 (accept_3_3 32 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 75 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 127
  (Polychromatic418967fa.accept_18_12_3_1_1_3685 30 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 127 (accept_3_3 29 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 127 (accept_3_3 26 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 127 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 75 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 127
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 127 (accept_3_3 23 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 127 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 127 (accept_3_3 20 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 127 (Polychromatic418967fa.accept_16_3_11_15_1_1963 19 75 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 127
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 127 (accept_3_3 17 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 127 (accept_3_3 14 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 75 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 127
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 127 (accept_3_3 11 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 127 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 127 (accept_3_3 8 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 75 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 127
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 127 (accept_3_3 5 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 127 (accept_3_3 2 75 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 127 (Polychromatic418967fa.accept_16_1_11_15_1_498 1 75 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 127)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 54 74 127 (Eq.refl Bool.true) (allA_of_3_1 54 74 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  55 73 127 (Eq.refl Bool.true) (allA_succ_of_accept 54 73 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 127 (accept_3_3 53 73 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 73 127
  (Polychromatic418967fa.accept_19_14_16_13_1_3488 52 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 127 (accept_3_3 50 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 127 (Polychromatic418967fa.accept_19_11_16_13_1_4853 49 73 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 127
  (Polychromatic418967fa.accept_19_10_16_13_1_3471 48 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 73 127 (accept_3_3 47 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 73 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 127 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 73 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 127 (accept_3_3 44 73 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 127 (Polychromatic418967fa.accept_13_4_8_10_1_671
  43 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 127 (accept_3_3 41 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 127 (accept_3_3 38 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 73 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 127
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 127 (accept_3_3 35 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 127 (accept_3_3 32 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 127 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 73 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 127 (accept_3_3 29 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 127 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 127 (Polychromatic418967fa.accept_49_27_24_29_1_6328 27 73 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 127 (accept_3_3 26 73 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 73 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 127
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 127 (accept_3_3 23 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 127 (Polychromatic418967fa.accept_15_6_13_7_1_222 21 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 127 (accept_3_3 20 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 73 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 127 (accept_3_3 17 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 127 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 127 (accept_3_3 14 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 127 (Polychromatic418967fa.accept_17_13_5_8_1_896 13 73 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 127
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 127 (accept_3_3 11 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 127 (accept_3_3 8 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 127 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 73 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 127 (accept_3_3 5 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  127 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 73 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 127 (Polychromatic418967fa.accept_17_3_5_8_1_1687 3 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 127 (accept_3_3 2 73 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 127 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 73 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 127)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 72 127 (Eq.refl Bool.true) (allA_succ_of_accept 55 72 127 (Polychromatic418967fa.accept_7_6_2_1_1_214
  55 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 127
  (Polychromatic418967fa.accept_10_4_2_7_1_373 54 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 72 127 (accept_3_3 53 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  72 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 72 127 (Polychromatic418967fa.accept_13_12_7_10_1_2662 51 72 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 127 (accept_3_3 50 72 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 127 (Polychromatic418967fa.accept_10_9_2_7_1_1096 49 72 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 127
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 127 (accept_3_3 47 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 127 (Polychromatic418967fa.accept_17_12_4_8_1_5073 46 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 127 (accept_3_3 44 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 127 (Polychromatic418967fa.accept_13_4_7_10_1_1200 43 72 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 127
  (Polychromatic418967fa.accept_13_3_7_10_1_668 42 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 127 (accept_3_3 41 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 127 (Polychromatic418967fa.accept_15_10_12_7_1_1358 40 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 127 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 127 (accept_3_3 38 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 127 (Polychromatic418967fa.accept_20_17_12_7_1_4759 37 72 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 127
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 127 (accept_3_3 35 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 127 (Polychromatic418967fa.accept_15_3_12_7_1_1346 33 72 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 127 (accept_3_3 32 72 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 72 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 127
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 30 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 127 (accept_3_3 29 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 127 (Polychromatic418967fa.accept_16_12_8_15_1_5119 28 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 127 (accept_3_3 26 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 127 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 72 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 127
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 127 (accept_3_3 23 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 127 (Polychromatic418967fa.accept_14_8_2_1_1_1652 22 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 127 (Polychromatic418967fa.accept_13_8_7_10_1_4362 21 72 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 127 (accept_3_3 20 72 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 127 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 72 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 127
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 127 (accept_3_3 17 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 127 (Polychromatic418967fa.accept_13_3_7_10_1_668 16 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 127 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 127 (accept_3_3 14 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 72 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 127
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 127 (accept_3_3 11 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 127 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 127 (accept_3_3 8 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 127 (Polychromatic418967fa.accept_16_7_8_15_1_6327 7 72 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 127
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 127 (accept_3_3 5 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  127 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 72 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 72 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 127 (accept_3_3 2 72 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 72 127 (Polychromatic418967fa.accept_16_1_8_15_1_1945 1 72 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 127))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 71 127 (Eq.refl Bool.true) (allA_of_3_1 57 71 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  58 70 127 (Eq.refl Bool.true) (allA_succ_of_accept 57 70 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 70 127 (accept_3_3 56 70 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 70 127 (Polychromatic418967fa.accept_16_7_6_15_1_495
  55 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 70 127
  (Polychromatic418967fa.accept_13_2_5_10_1_250 54 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 70 127 (accept_3_3 53 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  70 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 70 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 70 127 (accept_3_3 50 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 70 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 70 127
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 70 127 (accept_3_3 47 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  70 127 (Polychromatic418967fa.accept_11_2_4_6_1_2412 46 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 70 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 127 (accept_3_3 44 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 127 (Polychromatic418967fa.accept_13_4_5_10_1_1247 43 70 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 70 127 (accept_3_3 41 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  70 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 70 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 127 (accept_3_3 38 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 127
  (Polychromatic418967fa.accept_21_15_7_1_1_6326 36 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 70 127 (accept_3_3 35 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  70 127 (Polychromatic418967fa.accept_13_8_5_10_1_2701 34 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 70 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 127 (accept_3_3 32 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 70 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 127
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 127 (accept_3_3 29 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  70 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 70 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 127 (accept_3_3 26 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 127 (accept_3_3 23 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 127 (accept_3_3 20 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 127 (Polychromatic418967fa.accept_13_6_5_10_1_1213 19 70 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 127
  (Polychromatic418967fa.accept_15_3_10_7_1_2196 18 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 127 (accept_3_3 17 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 127 (accept_3_3 14 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 127
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 127 (accept_3_3 11 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  70 127 (Polychromatic418967fa.accept_17_10_2_8_1_6295 10 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 127 (accept_3_3 8 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 127 (Polychromatic418967fa.accept_16_7_6_15_1_495 7 70 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 70 127 (accept_3_3 5 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70
  127 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 70 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 70 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 127 (accept_3_3 2 70 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 70 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 127))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 69 127 (Eq.refl Bool.true) (allA_succ_of_accept 58 69 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 127 (accept_3_3 56 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 127 (Polychromatic418967fa.accept_17_4_1_8_1_5070 55 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 127 (accept_3_3 53 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 127
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 127 (accept_3_3 50 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 127 (accept_3_3 47 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 127
  (Polychromatic418967fa.accept_13_6_4_10_1_660 45 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 127 (accept_3_3 44 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 127 (accept_3_3 41 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 127 (accept_3_3 38 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 127 (Polychromatic418967fa.accept_16_4_5_15_1_5083 36 69 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 127 (accept_3_3 35 69 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 127
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 127 (accept_3_3 32 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 127 (accept_3_3 29 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 127
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 127 (accept_3_3 26 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 127 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 69 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 127 (accept_3_3 23 69 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 127 (accept_3_3 20 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 127 (accept_3_3 17 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 127
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 127 (accept_3_3 14 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 127 (accept_3_3 11 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 127
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 127 (accept_3_3 8 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  127 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 127 (accept_3_3 5 69 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 69
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 127 (accept_3_3 2 69 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 127 (Polychromatic418967fa.accept_13_1_4_10_1_622 1
  69 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  127))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 68 127 (Eq.refl Bool.true) (allA_of_3_1
  60 68 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 67 127 (Eq.refl Bool.true) (allA_succ_of_accept 60
  67 127 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 67 127 (accept_3_3 59 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 67 127 (Polychromatic418967fa.accept_13_6_2_10_1_1240 58 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 67 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 67 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 127 (accept_3_3 56 67 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 127 (Polychromatic418967fa.accept_13_3_2_10_1_2697
  55 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 127
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 127 (accept_3_3 53 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 127 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 127 (accept_3_3 50 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 127 (Polychromatic418967fa.accept_11_5_1_6_1_774 49 67 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 127
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 127 (accept_3_3 47 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 127 (Polychromatic418967fa.accept_14_4_11_1_1_940 46 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 127 (accept_3_3 44 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 67 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 127 (accept_3_3 41 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 127 (accept_3_3 38 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 127 (Polychromatic418967fa.accept_13_11_2_10_1_4399 37 67 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 127
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 127 (accept_3_3 35 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 127 (accept_3_3 32 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 67 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 127
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 127 (accept_3_3 29 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 127 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 127 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 127 (accept_3_3 26 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 67 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 127
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 127 (accept_3_3 23 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 127 (Polychromatic418967fa.accept_19_3_10_13_1_3482 22 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 127 (accept_3_3 20 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 67 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 127
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 127 (accept_3_3 17 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 127 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 127 (accept_3_3 14 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 127 (Polychromatic418967fa.accept_16_13_3_15_1_1931 13 67 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 127
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 127 (accept_3_3 11 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 127 (Polychromatic418967fa.accept_17_9_16_8_1_2721 9 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 127 (accept_3_3 8 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 127 (accept_3_3 5 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  127 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 67 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 127 (accept_3_3 2 67 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 127 (Polychromatic418967fa.accept_19_1_10_13_1_4880 1 67 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 127)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 66 127 (Eq.refl Bool.true) (allA_succ_of_accept 61 66 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 61
  66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 127
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 66 127 (accept_3_3 59 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  66 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 66 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 66 127 (accept_3_3 56 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 127 (Polychromatic418967fa.accept_19_17_9_13_1_6325 55 66 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 127
  (Polychromatic418967fa.accept_7_5_3_1_1_424 54 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 66 127 (accept_3_3 53 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  66 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 66 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 127 (accept_3_3 50 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 127
  (Polychromatic418967fa.accept_13_9_1_10_1_647 48 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 66 127 (accept_3_3 47 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  66 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 66 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 127 (accept_3_3 44 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 66 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 127
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 66 127 (accept_3_3 41 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  66 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 66 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 127 (accept_3_3 38 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 127
  (Polychromatic418967fa.accept_19_17_9_13_1_6325 36 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 127 (accept_3_3 35 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  66 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 66 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 127 (accept_3_3 32 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 66 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 127
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 66 127 (accept_3_3 29 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  66 127 (Polychromatic418967fa.accept_15_13_6_7_1_1369 28 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 66 127 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 66 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 127 (accept_3_3 26 66 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 127
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 66 127 (accept_3_3 23 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  66 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 66 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 127 (accept_3_3 20 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 66 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 127
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 127 (accept_3_3 17 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  66 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 127 (accept_3_3 14 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 127
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 66 127 (accept_3_3 11 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  66 127 (Polychromatic418967fa.accept_17_10_15_8_1_6324 10 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 66 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 127 (accept_3_3 8 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 66 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 127
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 127 (accept_3_3 5 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66
  127 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 66 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 66 127 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 127 (accept_3_3 2 66 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 66 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  127)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 65 127 (Eq.refl Bool.true)
  (allA_of_3_1 63 65 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 127 (allA_succ_of_accept 63 64 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 127 (accept_3_3 62 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 127 (Polychromatic418967fa.accept_10_1_4_7_1_374 61 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 127 (Polychromatic418967fa.accept_13_8_12_10_1_4414 60 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 127 (accept_3_3 59 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 127 (Polychromatic418967fa.accept_11_3_9_6_1_105 58 64 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 127 (accept_3_3 56 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 127 (Polychromatic418967fa.accept_15_10_4_7_1_3127 55 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 127 (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 127 (accept_3_3 53 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 127 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 64 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 127 (accept_3_3 50 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 127 (Polychromatic418967fa.accept_14_7_8_1_1_1621 49 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 127 (Polychromatic418967fa.accept_13_9_12_10_1_242 48 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 127 (accept_3_3 47 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 64 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 127 (accept_3_3 44 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 127 (Polychromatic418967fa.accept_10_3_4_7_1_353 43 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 127 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 127 (accept_3_3 41 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 127 (Polychromatic418967fa.accept_15_10_4_7_1_3127 40 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 127 (accept_3_3 38 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 127 (Polychromatic418967fa.accept_13_11_12_10_1_2652 37 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 127 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 127 (accept_3_3 35 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 127 (accept_3_3 32 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 127 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 127 (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 127 (accept_3_3 29 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 127 (Polychromatic418967fa.accept_13_2_12_10_1_2649 28 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 127 (accept_3_3 26 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 127 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 127 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 127 (accept_3_3 23 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 127 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 64 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 127 (accept_3_3 20 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 127 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 127 (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 127 (accept_3_3 17 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 127 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 127 (accept_3_3 14 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 127 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 127 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 127 (accept_3_3 11 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 127 (accept_3_3 8 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  127 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 64 127 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 127 (accept_3_3 5 64 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 127 (Polychromatic418967fa.accept_17_4_13_8_1_3874 4 64 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 127 (accept_3_3 2 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64
  127 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 64 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 127)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 127
  (allA_succ_of_accept 62 63 127 (accept_3_3 62 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 127 (Polychromatic418967fa.accept_17_10_12_8_1_2748 61 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 127 (Polychromatic418967fa.accept_13_8_11_10_1_636 60 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 127 (accept_3_3 59 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 63 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 127
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 127 (accept_3_3 56 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 127 (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 127 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 127 (accept_3_3 53 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 127
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 51 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 63 127 (accept_3_3 50 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 127 (Polychromatic418967fa.accept_15_4_3_7_1_713 49 63 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 63 127 (Polychromatic418967fa.accept_14_6_7_1_1_78 48 63 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 127 (accept_3_3 47 63 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 46
  63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 127
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 127 (accept_3_3 44 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 127 (Polychromatic418967fa.accept_13_4_11_10_1_1226 43 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 127 (Polychromatic418967fa.accept_13_3_11_10_1_2647 42 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 127 (accept_3_3 41 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 127
  (Polychromatic418967fa.accept_17_5_12_8_1_6304 39 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 127 (accept_3_3 38 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 127 (Polychromatic418967fa.accept_17_3_12_8_1_1688 37 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 127 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 127 (accept_3_3 35 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 127
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 127 (accept_3_3 32 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 127 (Polychromatic418967fa.accept_19_12_6_13_1_2305 31 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 127 (Polychromatic418967fa.accept_13_4_11_10_1_1226 30 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 127 (accept_3_3 29 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 127
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 127 (accept_3_3 26 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 127 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 127 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 127 (accept_3_3 23 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 127
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 127 (accept_3_3 20 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 127 (Polychromatic418967fa.accept_15_4_3_7_1_713 19 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 127 (Polychromatic418967fa.accept_23_18_17_12_1_6323 18 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 127 (accept_3_3 17 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 127
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 127 (accept_3_3 14 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 127 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 127 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 127 (accept_3_3 11 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 63 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 127
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 127 (accept_3_3 8 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  127 (Polychromatic418967fa.accept_19_7_6_13_1_6322 7 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 127 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 127 (accept_3_3 5 63 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 127
  (Polychromatic418967fa.accept_11_3_8_6_1_788 3 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 127 (accept_3_3 2 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  127 (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 63 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 127))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 127
  (allA_of_3_1 62 62 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 127 (allA_succ_of_accept 60 61 127
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 127 (accept_3_3 59 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 127 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 127 (accept_3_3 56 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 61 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 127 (accept_3_3 53 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 127 (accept_3_3 50 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 61 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 127
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 127 (accept_3_3 47 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 127 (accept_3_3 44 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 127 (Polychromatic418967fa.accept_23_20_15_12_1_6321 43 61 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 127 (accept_3_3 41 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 127 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 127 (accept_3_3 38 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 127 (Polychromatic418967fa.accept_21_16_19_1_1_6320 37 61 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 127
  (Polychromatic418967fa.accept_10_6_1_7_1_342 36 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 127 (accept_3_3 35 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 127 (accept_3_3 32 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 61 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 127 (accept_3_3 29 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 127 (Polychromatic418967fa.accept_16_12_13_15_1_1966 28 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 127 (accept_3_3 26 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 127 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 61 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 127
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 127 (accept_3_3 23 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 127 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 127 (accept_3_3 20 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 127 (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 61 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 127 (accept_3_3 17 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 127 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 127 (accept_3_3 14 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 61 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 127
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 127 (accept_3_3 11 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 127 (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 127 (accept_3_3 8 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 127 (Polychromatic418967fa.accept_19_7_4_13_1_6319 7 61 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 127 (accept_3_3 5 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  127 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 127 (accept_3_3 2 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 127 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 127)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 127 (allA_succ_of_accept 59 60 127 (accept_3_3 59 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 60 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 127 (accept_3_3 56 60 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 127
  (Polychromatic418967fa.accept_22_11_16_17_1_6318 55 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 60 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 127 (accept_3_3 53 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 60 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 60 127
  (Polychromatic418967fa.accept_8_3_4_7_1_475 51 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 60 127 (accept_3_3 50 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  60 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 60 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 127 (accept_3_3 47 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 127 (Polychromatic418967fa.accept_13_7_8_10_1_2663 46 60 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 60 127
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 60 127 (accept_3_3 44 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  60 127 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 60 127 (Polychromatic418967fa.accept_19_4_3_13_1_6317 42 60 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 127 (accept_3_3 41 60 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 60 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 60 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 60 127 (accept_3_3 38 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  60 127 (Polychromatic418967fa.accept_13_11_8_10_1_676 37 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 60 127 (Polychromatic418967fa.accept_16_4_12_15_1_6289 36 60 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 127 (accept_3_3 35 60 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 60 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 127
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 60 127 (accept_3_3 32 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  60 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 60 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 127 (accept_3_3 29 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 127 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 60 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 127
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 60 127 (accept_3_3 26 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  60 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 60 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 127 (accept_3_3 23 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 60 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 60 127 (accept_3_3 20 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  60 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 60 127 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 60 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 127 (accept_3_3 17 60 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 60 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 60 127
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 60 127 (accept_3_3 14 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  60 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 60 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 127 (accept_3_3 11 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 60 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 60 127
  (Polychromatic418967fa.accept_18_9_6_1_1_3687 9 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 60 127 (accept_3_3 8 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60
  127 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 60 127 (Polychromatic418967fa.accept_17_6_9_8_1_6316 6 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 127 (accept_3_3 5 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 60 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 127 (accept_3_3 2 60 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 127 (Polychromatic418967fa.accept_11_1_5_6_1_397 1
  60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  127)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 127 (allA_of_3_1 59 59 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 58 127 (allA_succ_of_accept 57 58 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 58 127 (accept_3_3 56 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  58 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 58 127 (Polychromatic418967fa.accept_13_2_6_10_1_2703 54 58 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 127 (accept_3_3 53 58 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 58 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 127 (accept_3_3 50 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 127 (accept_3_3 47 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 127 (Polychromatic418967fa.accept_16_14_10_15_1_3969 46 58 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 127 (accept_3_3 44 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 127 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 127 (accept_3_3 41 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 58 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 127 (accept_3_3 38 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 127 (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 127 (accept_3_3 35 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 58 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 127 (accept_3_3 32 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 127 (accept_3_3 29 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 58 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 127 (accept_3_3 26 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 127 (accept_3_3 23 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 127 (Polychromatic418967fa.accept_13_9_6_10_1_666 22 58 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 127 (accept_3_3 20 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 127 (Polychromatic418967fa.accept_10_9_8_7_1_714 19 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 127 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 58 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 127 (accept_3_3 17 58 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 58 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 127 (accept_3_3 14 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 127 (accept_3_3 11 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 58 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 127 (accept_3_3 8 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  127 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 127 (accept_3_3 5 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 58
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 127 (accept_3_3 2 58 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  127)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 127 (allA_succ_of_accept 56 57 127
  (accept_3_3 56 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 127
  (Polychromatic418967fa.accept_15_10_12_7_1_1358 55 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 127 (accept_3_3 53 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 51
  57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 127 (accept_3_3 50 57
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 127
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 127 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 127 (accept_3_3 47 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 127 (Polychromatic418967fa.accept_13_6_5_10_1_1213
  45 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 127 (accept_3_3 44
  57 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 127
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 127 (accept_3_3 41 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 127 (Polychromatic418967fa.accept_12_3_9_7_1_472
  39 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 127 (accept_3_3 38
  57 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 127
  (Polychromatic418967fa.accept_11_4_2_6_1_389 37 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 127 (Polychromatic418967fa.accept_15_6_12_7_1_1360 36 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 127 (accept_3_3 35 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 33
  57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 127 (accept_3_3 32 57
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 127
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 127 (accept_3_3 29 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 127 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 127 (accept_3_3 26
  57 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 127
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 127 (accept_3_3 23 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 127 (Polychromatic418967fa.accept_13_8_5_10_1_2701
  21 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 127 (accept_3_3 20
  57 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 127
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 19 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 127 (accept_3_3 17 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 15
  57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 127 (accept_3_3 14 57
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 127
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 127 (Polychromatic418967fa.accept_18_12_3_1_1_3685 12 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 127 (accept_3_3 11 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 127 (Polychromatic418967fa.accept_17_9_6_8_1_6315 9
  57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 127 (accept_3_3 8 57 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 7
  57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 127 (accept_3_3 5 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 127 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 127 (accept_3_3 2 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 127 (Polychromatic418967fa.accept_23_1_11_12_1_6314 1 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 127)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 127 (allA_of_3_1 56 56 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 127
  (allA_succ_of_accept 54 55 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 127 (accept_3_3 53 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 127 (Polychromatic418967fa.accept_10_2_5_7_1_1124 52 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 51
  55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 127 (accept_3_3 50 55
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 127
  (Polychromatic418967fa.accept_14_7_13_1_1_922 49 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 127 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 127 (accept_3_3 47 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 127 (Polychromatic418967fa.accept_13_7_3_10_1_656 46 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 127 (Polychromatic418967fa.accept_13_6_3_10_1_698
  45 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 127 (accept_3_3 44
  55 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 127
  (Polychromatic418967fa.accept_10_3_5_7_1_330 43 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 55 127 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 127 (accept_3_3 41 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 55 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 127
  (Polychromatic418967fa.accept_23_16_9_12_1_6313 39 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 127 (accept_3_3 38 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 127 (Polychromatic418967fa.accept_27_9_1_19_1_4355 36 55 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 127 (accept_3_3 35 55 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 127 (Polychromatic418967fa.accept_15_4_10_7_1_1356 34 55
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 127
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 127 (accept_3_3 32 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 127 (Polychromatic418967fa.accept_15_1_10_7_1_4087 31 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 127 (accept_3_3 29 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 127 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 55 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 127
  (Polychromatic418967fa.accept_15_12_10_7_1_1357 27 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 127 (accept_3_3 26 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 127 (Polychromatic418967fa.accept_19_6_17_13_1_2323 25 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 127 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 55 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 127 (accept_3_3 23 55 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 127 (Polychromatic418967fa.accept_10_2_5_7_1_1124 22 55 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 127
  (Polychromatic418967fa.accept_14_7_13_1_1_922 21 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 127 (accept_3_3 20 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 127 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 127 (accept_3_3 17 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 55 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 127
  (Polychromatic418967fa.accept_13_2_3_10_1_658 15 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 127 (accept_3_3 14 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 127 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 127 (accept_3_3 11 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 127 (Polychromatic418967fa.accept_20_10_15_7_1_6312 10 55 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 127
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 127 (accept_3_3 8 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  127 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 55 127 (Polychromatic418967fa.accept_13_6_3_10_1_698 6 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 127 (accept_3_3 5 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 127 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 55 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 127
  (Polychromatic418967fa.accept_10_3_5_7_1_330 3 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 127 (accept_3_3 2 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55
  127 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 55 127))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 127
  (allA_succ_of_accept 53 54 127 (accept_3_3 53 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  54 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 127 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 127 (accept_3_3 50 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 127
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 127 (accept_3_3 47 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 127 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 127 (accept_3_3 44 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 127 (Polychromatic418967fa.accept_10_3_4_7_1_353 43 54 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 127
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 127 (accept_3_3 41 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 127 (Polychromatic418967fa.accept_19_2_16_13_1_6311 40 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 127 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 127 (accept_3_3 38 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 127
  (Polychromatic418967fa.accept_19_17_16_13_1_4900 36 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 54 127 (accept_3_3 35 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 54 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 54 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 127 (accept_3_3 32 54 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 31
  54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 127
  (Polychromatic418967fa.accept_17_13_3_8_1_6310 30 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 127 (accept_3_3 29 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 127 (Polychromatic418967fa.accept_15_13_9_7_1_2194 28 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 127 (accept_3_3 26 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 127
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 127 (accept_3_3 23 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 127 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 127 (accept_3_3 20 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 127 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 54 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 127
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 127 (accept_3_3 17 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 127 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 127 (Polychromatic418967fa.accept_19_15_16_13_1_1336 15 54 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 127 (accept_3_3 14 54 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 127
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 127 (accept_3_3 11 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 127 (accept_3_3 8 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 127 (Polychromatic418967fa.accept_16_7_6_15_1_495 7 54 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 127
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 127 (accept_3_3 5 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  127 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 54 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 54 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 127 (accept_3_3 2 54 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 54 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 127))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 127 (allA_of_3_1 53 53 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 127
  (allA_succ_of_accept 51 52 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 127 (accept_3_3 50 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 127 (Polychromatic418967fa.accept_9_3_7_1_1_143 48
  52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 127 (accept_3_3 47 52
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 127 (Polychromatic418967fa.accept_7_4_3_1_1_87
  46 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 52 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 52 127 (accept_3_3 44 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  52 127 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 52 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 127 (accept_3_3 41 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 52 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 52 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 52 127 (accept_3_3 38 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  52 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 52 127 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 127 (accept_3_3 35 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 127 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 52 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 127 (accept_3_3 32 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 127 (accept_3_3 29 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 127 (Polychromatic418967fa.accept_16_12_4_15_1_5091 28 52 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 52 127 (accept_3_3 26 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  52 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 52 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 127 (accept_3_3 23 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 52 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 127 (accept_3_3 20 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 127 (accept_3_3 17 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 52 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 127 (accept_3_3 14 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  52 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 52 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 127 (accept_3_3 11 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 52 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 127 (accept_3_3 8 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52
  127 (Polychromatic418967fa.accept_17_7_1_8_1_6280 7 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 52 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 127 (accept_3_3 5 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 52 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 52 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 52 127 (accept_3_3 2 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52
  127 (Polychromatic418967fa.accept_19_1_14_13_1_6294 1 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 52 127)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 127
  (allA_succ_of_accept 50 51 127 (accept_3_3 50 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  51 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 127 (accept_3_3 47 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 51 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 127
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 127 (accept_3_3 44 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 127 (Polychromatic418967fa.accept_15_12_6_7_1_1353 42 51 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 127 (accept_3_3 41 51 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 127 (accept_3_3 38 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 127 (Polychromatic418967fa.accept_13_11_12_10_1_2652 37 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 127 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 127 (accept_3_3 35 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 51 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 127
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 127 (accept_3_3 32 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 127 (accept_3_3 29 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 127
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 127 (accept_3_3 26 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 127 (accept_3_3 23 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 51 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 127 (accept_3_3 20 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 127 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 127 (Polychromatic418967fa.accept_16_2_3_15_1_6309 18 51 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 127 (accept_3_3 17 51 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 127
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 127 (accept_3_3 14 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 127 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 127 (accept_3_3 11 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 51 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 127
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 127 (accept_3_3 8 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  127 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 127 (accept_3_3 5 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 127 (accept_3_3 2 51 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 127 (Polychromatic418967fa.accept_11_1_7_6_1_378 1
  51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  127))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 127 (allA_of_3_1 50 50 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 127 (allA_succ_of_accept 48 49 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 127 (accept_3_3 47 49 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 127
  (Polychromatic418967fa.accept_11_1_5_6_1_397 45 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 127 (accept_3_3 44 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 127 (accept_3_3 41 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 127 (Polychromatic418967fa.accept_15_10_4_7_1_3127 40 49 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 127
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 127 (accept_3_3 38 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 127 (Polychromatic418967fa.accept_16_5_1_15_1_3922 37 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 127 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 127 (accept_3_3 35 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 127 (accept_3_3 32 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 127 (Polychromatic418967fa.accept_19_12_11_13_1_4885 31 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 127 (accept_3_3 29 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 127 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 49 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 127
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 127 (accept_3_3 26 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 127 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 127 (accept_3_3 23 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 127
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 127 (accept_3_3 20 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 127 (Polychromatic418967fa.accept_21_19_7_1_1_3329 19 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 127 (accept_3_3 17 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 127 (accept_3_3 14 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 127 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 127 (accept_3_3 11 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 127
  (Polychromatic418967fa.accept_23_9_3_12_1_6308 9 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 127 (accept_3_3 8 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  127 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 127 (accept_3_3 5 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 127 (Polychromatic418967fa.accept_21_4_7_1_1_6307 4 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 49
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 127 (accept_3_3 2 49 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 127 (Polychromatic418967fa.accept_11_1_5_6_1_397 1
  49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  127))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 127 (allA_succ_of_accept 47 48 127 (accept_3_3 47
  48 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 127
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 46 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 127 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 127 (accept_3_3 44 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 48 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 42
  48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 127 (accept_3_3 41 48
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 127
  (Polychromatic418967fa.accept_7_5_6_1_1_407 40 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 48 127 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 127 (accept_3_3 38 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 48 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 48 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 127 (Polychromatic418967fa.accept_21_15_6_1_1_6306
  36 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 127 (accept_3_3 35
  48 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 127
  (Polychromatic418967fa.accept_9_7_3_1_1_386 34 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 48 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 127 (accept_3_3 32 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 48 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 48 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 30
  48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 127 (accept_3_3 29 48
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 127
  (Polychromatic418967fa.accept_17_11_14_8_1_2729 28 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 48 127 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 127 (accept_3_3 26 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 48 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 48 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 24
  48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 127 (accept_3_3 23 48
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 127
  (Polychromatic418967fa.accept_9_4_3_1_1_154 22 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 48 127 (Polychromatic418967fa.accept_14_7_6_1_1_1656 21 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 127 (accept_3_3 20 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 48 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 48 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 127
  (Polychromatic418967fa.accept_22_18_4_17_1_6305 18 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 127 (accept_3_3 17 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 48 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 127 (accept_3_3 14 48 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 127
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 127 (accept_3_3 11 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 127 (Polychromatic418967fa.accept_15_10_3_7_1_715 10 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 127 (accept_3_3 8 48 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 127
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 127 (accept_3_3 5 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  127 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 127 (Polychromatic418967fa.accept_18_3_12_1_1_3787 3 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 127 (accept_3_3 2 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 127 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 48 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 127)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 127 (allA_of_3_1 47 47 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 127 (allA_succ_of_accept 45 46
  127 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 127 (accept_3_3 44 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 127 (Polychromatic418967fa.accept_10_3_6_7_1_2188 43 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 127 (Polychromatic418967fa.accept_13_3_7_10_1_668 42 46 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 127 (accept_3_3 41 46 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 46 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 127 (accept_3_3 38 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 127 (Polychromatic418967fa.accept_15_6_1_7_1_4079 36 46 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 127 (accept_3_3 35 46 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 127 (Polychromatic418967fa.accept_13_8_7_10_1_4362 34 46 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 127 (accept_3_3 32 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 127 (Polychromatic418967fa.accept_13_4_7_10_1_1200 30 46 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 127 (accept_3_3 29 46 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 46 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 127 (accept_3_3 26 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 46 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 127 (accept_3_3 23 46 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 127 (Polychromatic418967fa.accept_17_5_12_8_1_6304 22 46 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 127 (accept_3_3 20 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 127 (Polychromatic418967fa.accept_19_18_8_13_1_6303 18 46 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 127 (accept_3_3 17 46 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 46 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 127 (accept_3_3 14 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 46 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 127 (accept_3_3 11 46 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 46 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 127 (accept_3_3 8 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  127 (Polychromatic418967fa.accept_16_7_14_15_1_2932 7 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 46 127 (Polychromatic418967fa.accept_15_6_1_7_1_4079 6 46 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 127 (accept_3_3 5 46 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 127 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 46 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 46 127 (accept_3_3 2 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46
  127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 127)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 127 (allA_succ_of_accept 44 45 127
  (accept_3_3 44 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 127
  (Polychromatic418967fa.accept_10_3_5_7_1_330 43 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 127 (accept_3_3 41 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 39
  45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 127 (accept_3_3 38 45
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 127 (Polychromatic418967fa.accept_7_2_3_1_1_10
  37 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 127
  (Polychromatic418967fa.accept_17_2_11_8_1_2726 36 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 127 (accept_3_3 35 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 127 (accept_3_3 32 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 127 (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 45 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 127 (accept_3_3 29 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 127 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 127 (accept_3_3 26 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 45 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 127
  (Polychromatic418967fa.accept_18_6_9_1_1_3769 24 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 127 (accept_3_3 23 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 127 (Polychromatic418967fa.accept_18_3_9_1_1_3690 21 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 127 (accept_3_3 20 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 45 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 127 (accept_3_3 17 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 127 (Polychromatic418967fa.accept_12_3_9_7_1_472 15 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 127 (accept_3_3 14 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 127 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 45 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 127
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 127 (accept_3_3 11 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 127 (accept_3_3 8 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 127 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 45 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 127 (accept_3_3 5 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 127 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 127 (accept_3_3 2 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 127 (Polychromatic418967fa.accept_17_1_11_8_1_2725 1 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 127))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  127 (allA_of_3_1 44 44 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 127 (allA_succ_of_accept 42 43 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 127 (accept_3_3 41 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 127 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 127 (accept_3_3 38 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 127 (Polychromatic418967fa.accept_13_11_4_10_1_3440 37 43 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 127
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 127 (accept_3_3 35 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 127 (Polychromatic418967fa.accept_10_4_3_7_1_1110 34 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 127 (accept_3_3 32 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 43 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 127
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 127 (accept_3_3 29 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 127 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 127 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 127 (accept_3_3 26 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 127 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 43 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 127 (accept_3_3 23 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 127 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 127 (accept_3_3 20 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 127 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 43 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 127
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 127 (accept_3_3 17 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 127 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 127 (accept_3_3 14 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 43 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 127
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 127 (accept_3_3 11 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 127 (Polychromatic418967fa.accept_16_10_11_15_1_6302 10 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 127 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 127 (accept_3_3 8 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 127 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 43 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 127 (accept_3_3 5 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  127 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 127 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 43 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 127 (accept_3_3 2 43 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 127 (Polychromatic418967fa.accept_13_1_4_10_1_622 1 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 127))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 127
  (allA_succ_of_accept 41 42 127 (accept_3_3 41 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 42 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 127 (accept_3_3 38 42 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 127
  (Polychromatic418967fa.accept_11_3_9_6_1_105 36 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 127 (accept_3_3 35 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 127 (accept_3_3 32 42 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 42 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 127 (accept_3_3 29 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 127 (Polychromatic418967fa.accept_13_2_3_10_1_658 28 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 127 (Polychromatic418967fa.accept_16_11_10_15_1_6301 27 42 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 127 (accept_3_3 26 42 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 127
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 127 (accept_3_3 23 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 127 (accept_3_3 20 42 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 127 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 42 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 127
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 127 (accept_3_3 17 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 127 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 42 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 127 (accept_3_3 14 42 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 127 (accept_3_3 11 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 127 (Polychromatic418967fa.accept_15_10_12_7_1_1358 10 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 127 (accept_3_3 8 42 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 42 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 127
  (Polychromatic418967fa.accept_13_6_3_10_1_698 6 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 127 (accept_3_3 5 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  127 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 42 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 127 (accept_3_3 2 42 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 127)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 127
  (allA_of_3_1 41 41 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 127 (allA_succ_of_accept 39 40 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 127 (accept_3_3 38 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 127 (Polychromatic418967fa.accept_13_11_1_10_1_648 37 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 127 (Polychromatic418967fa.accept_16_4_8_15_1_1113 36 40 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 127 (accept_3_3 35 40 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 40 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 127 (accept_3_3 32 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 40 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 127 (accept_3_3 29 40 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 127 (Polychromatic418967fa.accept_16_12_8_15_1_5119 28 40 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 127 (accept_3_3 26 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 127 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 40 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 127 (accept_3_3 23 40 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 40 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 127 (accept_3_3 20 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 127 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 127 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 40 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 127 (accept_3_3 17 40 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 40 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 127 (accept_3_3 14 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 40 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 127 (accept_3_3 11 40 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 40 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 127 (accept_3_3 8 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  127 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 40 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 127 (accept_3_3 5 40 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 127 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 40 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 127 (accept_3_3 2 40 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 127 (Polychromatic418967fa.accept_11_1_7_6_1_378 1
  40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  127)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 127 (allA_succ_of_accept 38 39 127 (accept_3_3 38 39 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 127 (Polychromatic418967fa.accept_17_3_5_8_1_1687
  37 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 127
  (Polychromatic418967fa.accept_21_15_18_1_1_6300 36 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 127 (accept_3_3 35 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 39 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 127 (accept_3_3 32 39 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 39 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 127
  (Polychromatic418967fa.accept_16_14_7_15_1_3947 30 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 127 (accept_3_3 29 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 127 (Polychromatic418967fa.accept_16_11_7_15_1_1998 27 39 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 127 (accept_3_3 26 39 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 39 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 127
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 127 (accept_3_3 23 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 127 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 39 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 127 (accept_3_3 20 39 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 39 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 127
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 127 (accept_3_3 17 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 39 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 127 (accept_3_3 14 39 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 39 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 127
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 127 (accept_3_3 11 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 127 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 39 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 127 (accept_3_3 8 39 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 39 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 127
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 127 (accept_3_3 5 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 127 (accept_3_3 2 39 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 127 (Polychromatic418967fa.accept_15_1_9_7_1_3130 1 39 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 127))))))))))))))))))))))))))))))))))))))) (allB_succ 38 127
  (allA_of_3_1 38 38 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 127 (allA_succ_of_accept 36 37 127
  (Polychromatic418967fa.accept_14_8_9_1_1_3313 36 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 127 (accept_3_3 35 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 127 (Polychromatic418967fa.accept_16_1_5_15_1_2918 33 37 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 127 (accept_3_3 32 37 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 37 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 127 (accept_3_3 29 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 127 (Polychromatic418967fa.accept_13_2_11_10_1_1881 28 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 37 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 127 (accept_3_3 26 37 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 127 (Polychromatic418967fa.accept_13_12_11_10_1_2711 25 37 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 127
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 127 (accept_3_3 23 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 127 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 37 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 127 (accept_3_3 20 37 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 127 (Polychromatic418967fa.accept_20_19_17_7_1_6299 19 37
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 127 (accept_3_3 17 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 127 (Polychromatic418967fa.accept_13_3_11_10_1_2647 16 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 127 (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 37 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 127 (accept_3_3 14 37 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 37 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 127
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 37 127 (accept_3_3 11 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 37 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 127 (Polychromatic418967fa.accept_19_9_18_13_1_4931 9 37 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 127 (accept_3_3 8 37 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 127 (Polychromatic418967fa.accept_21_7_16_1_1_6298
  7 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 127 (accept_3_3 5 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  127 (Polychromatic418967fa.accept_13_4_11_10_1_1226 4 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 37 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 37 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 127 (accept_3_3 2 37 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 127 (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 37 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 127))))))))))))))))))))))))))))))))))))) (allB_succ
  36 127 (allA_succ_of_accept 35 36 127 (accept_3_3 35 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 127 (Polychromatic418967fa.accept_19_15_17_13_1_4901 34 36 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 127 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 36 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 127 (accept_3_3 32 36 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 127 (Polychromatic418967fa.accept_10_1_6_7_1_710
  31 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 127
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 127 (accept_3_3 29 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 127 (Polychromatic418967fa.accept_15_13_6_7_1_1369 28 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 127 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 36 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 127 (accept_3_3 26 36 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 127 (Polychromatic418967fa.accept_19_6_17_13_1_2323 25 36 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 127
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 127 (accept_3_3 23 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 127 (Polychromatic418967fa.accept_23_22_13_12_1_6297 22 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 127 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 36 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 127 (accept_3_3 20 36 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 127 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 36 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 127
  (Polychromatic418967fa.accept_19_18_17_13_1_6296 18 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 36 127 (accept_3_3 17 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 127 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 36 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 127 (Polychromatic418967fa.accept_19_15_17_13_1_4901 15 36
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 127 (accept_3_3 14 36 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 127 (Polychromatic418967fa.accept_10_3_6_7_1_2188
  13 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 127
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 127 (accept_3_3 11 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 127 (Polychromatic418967fa.accept_17_10_2_8_1_6295 10 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 127 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 36 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 127 (accept_3_3 8 36 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 127 (Polychromatic418967fa.accept_14_7_8_1_1_1621 7 36 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 127
  (Polychromatic418967fa.accept_19_6_17_13_1_2323 6 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 127 (accept_3_3 5 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  127 (Polychromatic418967fa.accept_19_4_17_13_1_4929 4 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 127 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 36 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 127 (accept_3_3 2 36 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 127 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 36 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 127)))))))))))))))))))))))))))))))))))) (allB_succ 35
  127 (allA_of_3_1 35 35 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 127 (allA_succ_of_accept 33 34 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 127 (accept_3_3 32 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 34 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 127 (accept_3_3 29 34 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 127 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 34 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 127 (accept_3_3 26 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 34 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 127 (accept_3_3 23 34 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 34 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 127 (accept_3_3 20 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 127 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 34 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 127 (accept_3_3 17 34 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 34 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 127 (accept_3_3 14 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 34 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 127 (accept_3_3 11 34 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 127 (Polychromatic418967fa.accept_15_10_4_7_1_3127 10 34 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 127 (accept_3_3 8 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  127 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 34 127 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 34 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 127 (accept_3_3 5 34 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 34 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 34 127 (accept_3_3 2 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34
  127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 127)))))))))))))))))))))))))))))))))) (allB_succ 33 127 (allA_succ_of_accept 32 33 127 (accept_3_3 32 33
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 127 (Polychromatic418967fa.accept_7_3_5_1_1_72
  31 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 127 (accept_3_3 29 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 33 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 127 (accept_3_3 26 33 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 127 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 33 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 127
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 127 (accept_3_3 23 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 33 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 127 (accept_3_3 20 33 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 127 (Polychromatic418967fa.accept_15_4_3_7_1_713 19 33 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 127 (accept_3_3 17 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 127 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 33 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 127 (accept_3_3 14 33 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 33 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 127 (accept_3_3 11 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 127 (Polychromatic418967fa.accept_17_9_16_8_1_2721 9 33 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 127 (accept_3_3 8 33 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 33 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 127 (accept_3_3 5 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 33 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 127 (accept_3_3 2 33 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 127 (Polychromatic418967fa.accept_19_1_14_13_1_6294 1 33 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 127))))))))))))))))))))))))))))))))) (allB_succ 32 127
  (allA_of_3_1 32 32 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 127 (allA_succ_of_accept 30 31 127
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 127 (accept_3_3 29 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 127 (Polychromatic418967fa.accept_13_2_5_10_1_250 28 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 127 (Polychromatic418967fa.accept_23_4_8_12_1_6293 27 31 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 127 (accept_3_3 26 31 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 31 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 127 (accept_3_3 23 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 127 (Polychromatic418967fa.accept_19_3_12_13_1_2292 22 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 31 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 127 (accept_3_3 20 31 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 127
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 127 (accept_3_3 17 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 127 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 31 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 127 (accept_3_3 14 31 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 127 (Polychromatic418967fa.accept_21_13_10_1_1_6292 13 31 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 127
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 127 (accept_3_3 11 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 127 (Polychromatic418967fa.accept_15_10_1_7_1_5207 10 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 127 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 31 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 127 (accept_3_3 8 31 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 127
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 127 (accept_3_3 5 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  127 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 31 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 127 (accept_3_3 2 31 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 127 (Polychromatic418967fa.accept_19_1_12_13_1_6279 1 31 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 127))))))))))))))))))))))))))))))) (allB_succ 30 127
  (allA_succ_of_accept 29 30 127 (accept_3_3 29 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 127 (Polychromatic418967fa.accept_20_8_10_7_1_6291 28 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 30 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 127 (accept_3_3 26 30 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 127
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 127 (accept_3_3 23 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 127 (accept_3_3 20 30 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 127 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 30 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 127
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 127 (accept_3_3 17 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 30 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 127 (accept_3_3 14 30 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 127
  (Polychromatic418967fa.accept_19_12_11_13_1_4885 12 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 30 127 (accept_3_3 11 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 30 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 127 (accept_3_3 8 30 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 7
  30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 127
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 127 (accept_3_3 5 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  127 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 30 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 30 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 127 (accept_3_3 2 30 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 30 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 127)))))))))))))))))))))))))))))) (allB_succ 29 127 (allA_of_3_1
  29 29 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 127 (allA_succ_of_accept 27 28 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 127 (accept_3_3 26 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 127 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 127 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 28 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 127 (accept_3_3 23 28 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 28 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 127 (accept_3_3 20 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 127 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 127 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 28 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 127 (accept_3_3 17 28 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 127 (Polychromatic418967fa.accept_13_3_2_10_1_2697 16 28 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 127 (accept_3_3 14 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 127 (Polychromatic418967fa.accept_16_13_12_15_1_6290 13 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 127 (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 28 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 127 (accept_3_3 11 28 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 127 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 28 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 127 (accept_3_3 8 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  127 (Polychromatic418967fa.accept_19_7_9_13_1_4836 7 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 28 127 (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 28 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 127 (accept_3_3 5 28 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 127 (Polychromatic418967fa.accept_16_4_12_15_1_6289 4 28 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 127 (accept_3_3 2 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28
  127 (Polychromatic418967fa.accept_17_1_11_8_1_2725 1 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 28 127)))))))))))))))))))))))))))) (allB_succ 27 127 (allA_succ_of_accept 26 27 127 (accept_3_3
  26 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 127
  (Polychromatic418967fa.accept_15_10_12_7_1_1358 25 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 27 127 (Polychromatic418967fa.accept_13_11_1_10_1_648 24 27 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 127 (accept_3_3 23 27 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 27 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 27 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 127 (Polychromatic418967fa.accept_11_10_5_6_1_1842
  21 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 127 (accept_3_3 20
  27 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 127
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 27 127 (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 27 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 127 (accept_3_3 17 27 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 27 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 127
  (Polychromatic418967fa.accept_17_15_10_8_1_1708 15 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 127 (accept_3_3 14 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 127 (Polychromatic418967fa.accept_26_13_1_23_1_6288 13 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 127 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 127 (accept_3_3 11 27 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 27 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 127
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 127 (accept_3_3 8 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  127 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 127 (Polychromatic418967fa.accept_15_6_12_7_1_1360 6 27 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 127 (accept_3_3 5 27 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 127
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 127 (accept_3_3 2 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  127 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 127))))))))))))))))))))))))))) (allB_succ 26 127 (allA_of_3_1 26 26 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 25 127 (allA_succ_of_accept 24 25 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 25 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 127 (accept_3_3 23 25 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 127
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 127 (accept_3_3 20 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 127 (accept_3_3 17 25 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 127 (Polychromatic418967fa.accept_15_1_10_7_1_4087 16 25 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 127 (accept_3_3 14 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 127 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 127 (accept_3_3 11 25 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 127
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 127 (accept_3_3 8 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  127 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 127 (accept_3_3 5 25 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 25 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 127
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 127 (accept_3_3 2 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  127 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 25 127))))))))))))))))))))))))) (allB_succ 24 127 (allA_succ_of_accept 23 24 127 (accept_3_3 23
  24 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 127
  (Polychromatic418967fa.accept_9_4_6_1_1_393 22 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 24 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 127 (accept_3_3 20 24 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 24 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 24 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 18
  24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 127 (accept_3_3 17 24
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 127 (Polychromatic418967fa.accept_7_2_3_1_1_10
  16 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 127
  (Polychromatic418967fa.accept_11_4_2_6_1_389 15 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 24 127 (accept_3_3 14 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  24 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 24 127 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 24 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 127 (accept_3_3 11 24 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 127 (Polychromatic418967fa.accept_19_10_5_13_1_6287 10 24 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 127
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 24 127 (accept_3_3 8 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24
  127 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 24 127 (Polychromatic418967fa.accept_21_6_3_1_1_6286 6 24 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 127 (accept_3_3 5 24 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 24 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 24 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 127 (accept_3_3 2 24 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 127 (Polychromatic418967fa.accept_10_1_4_7_1_374 1
  24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 127))))))))))))))))))))))))
  (allB_succ 23 127 (allA_of_3_1 23 23 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 127
  (allA_succ_of_accept 21 22 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 127 (accept_3_3 20 22 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 22 127 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 22 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 22 127 (Polychromatic418967fa.accept_20_18_2_7_1_6285
  18 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 127 (accept_3_3 17
  22 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 127
  (Polychromatic418967fa.accept_9_7_4_1_1_391 16 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 22 127 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 22 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 127 (accept_3_3 14 22 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 22 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 12
  22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 127 (accept_3_3 11 22
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 127
  (Polychromatic418967fa.accept_19_10_3_13_1_6284 10 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 22 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 127 (accept_3_3 8 22 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 22 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 22 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 127 (Polychromatic418967fa.accept_9_6_4_1_1_390 6
  22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 127 (accept_3_3 5 22 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 127 (Polychromatic418967fa.accept_10_4_2_7_1_373 4
  22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 127 (accept_3_3 2 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22
  127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 127)))))))))))))))))))))) (allB_succ 21 127 (allA_succ_of_accept 20 21 127 (accept_3_3 20 21 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 127 (Polychromatic418967fa.accept_22_19_21_17_1_6283 19 21
  127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 127 (accept_3_3 17 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  21 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 21 127 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 21 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 127 (accept_3_3 14 21 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 127 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 21 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 127
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 127 (accept_3_3 11 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 127 (Polychromatic418967fa.accept_18_9_3_1_1_2559 9 21 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 127 (accept_3_3 8 21 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 21 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 127 (accept_3_3 5 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 127 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 21 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 127 (accept_3_3 2 21 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 127 (Polychromatic418967fa.accept_15_1_6_7_1_6282 1 21 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 127))))))))))))))))))))) (allB_succ 20 127 (allA_of_3_1 20 20
  127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 127 (allA_succ_of_accept 18 19 127
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 127 (accept_3_3 17 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 127 (Polychromatic418967fa.accept_13_3_6_10_1_2658 16 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 127 (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 19 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 127 (accept_3_3 14 19 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 127 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 19 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 127
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 127 (accept_3_3 11 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 127 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 19 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 127 (accept_3_3 8 19 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 127 (Polychromatic418967fa.accept_16_7_3_15_1_2940 7 19 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 127
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 127 (accept_3_3 5 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  127 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 19 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 127 (accept_3_3 2 19 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 127 (Polychromatic418967fa.accept_24_1_19_7_1_6281 1 19 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 127))))))))))))))))))) (allB_succ 18 127 (allA_succ_of_accept 17
  18 127 (accept_3_3 17 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 127
  (Polychromatic418967fa.accept_19_16_18_13_1_4855 16 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 18 127 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 18 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 127 (accept_3_3 14 18 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 127
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 18 127 (accept_3_3 11 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  18 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 18 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 127 (accept_3_3 8 18 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 127 (Polychromatic418967fa.accept_17_7_1_8_1_6280 7 18 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 127
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 6 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 127 (accept_3_3 5 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18
  127 (Polychromatic418967fa.accept_13_4_5_10_1_1247 4 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 127 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 18 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 127 (accept_3_3 2 18 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 127)))))))))))))))))) (allB_succ 17 127 (allA_of_3_1
  17 17 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 127 (allA_succ_of_accept 15 16 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 127 (accept_3_3 14 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 127 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 16 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 127 (accept_3_3 11 16 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 16 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 127 (accept_3_3 8 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  127 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 16 127 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 16 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 127 (accept_3_3 5 16 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 16 127 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 16 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 16 127 (accept_3_3 2 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16
  127 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 127)))))))))))))))) (allB_succ 15 127 (allA_succ_of_accept 14 15 127 (accept_3_3 14 15 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 127 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 15 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 127
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 15 127 (accept_3_3 11 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  15 127 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 15 127 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 15 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 127 (accept_3_3 8 15 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 127 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 15 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 127
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 127 (accept_3_3 5 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  127 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 15 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 127 (accept_3_3 2 15 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 127 (Polychromatic418967fa.accept_20_1_15_7_1_3405 1 15 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 127))))))))))))))) (allB_succ 14 127 (allA_of_3_1 14 14 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 127 (allA_succ_of_accept 12 13 127
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 127 (accept_3_3 11 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 127 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 127 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 13 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 127 (accept_3_3 8 13 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 127 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 13 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 127 (accept_3_3 5 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  127 (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 127 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 13 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 127 (accept_3_3 2 13 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 127 (Polychromatic418967fa.accept_23_1_13_12_1_3002 1 13 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 127))))))))))))) (allB_succ 12 127
  (allA_succ_of_accept 11 12 127 (accept_3_3 11 12 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  12 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 12 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 127 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 12 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 127 (accept_3_3 8 12 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 127 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 127
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 12 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 127 (accept_3_3 5 12 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12
  127 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 12 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 12 127 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 127 (accept_3_3 2 12 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 12 127 (Polychromatic418967fa.accept_19_1_12_13_1_6279 1 12 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 127)))))))))))) (allB_succ 11 127 (allA_of_3_1 11 11 127
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 127 (allA_succ_of_accept 9 10 127
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 127 (accept_3_3 8 10 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  127 (Polychromatic418967fa.accept_21_7_10_1_1_6278 7 10 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 10 127 (Polychromatic418967fa.accept_19_6_10_13_1_4839 6 10 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 127 (accept_3_3 5 10 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 10 127 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 10 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 10 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 10 127 (accept_3_3 2 10 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10
  127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 127)))))))))) (allB_succ 9 127 (allA_succ_of_accept 8 9 127 (accept_3_3 8 9 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 127 (Polychromatic418967fa.accept_19_7_9_13_1_4836 7 9 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 127
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 127 (accept_3_3 5 9 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 127
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 127 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 9 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 127 (accept_3_3 2 9 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 127 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 9 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 127))))))))) (allB_succ 8 127 (allA_of_3_1 8 8 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 127 (allA_succ_of_accept 6 7 127
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 7 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 127 (accept_3_3 5 7 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 127
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 127 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 7 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 127 (accept_3_3 2 7 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 127 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 7 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 127))))))) (allB_succ 6 127 (allA_succ_of_accept 5 6 127
  (accept_3_3 5 6 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 127
  (Polychromatic418967fa.accept_9_4_6_1_1_393 4 6 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 127 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 6 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 127 (accept_3_3 2 6 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 127 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 127)))))) (allB_succ 5 127 (allA_of_3_1 5 5 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 127 (allA_succ_of_accept 3 4 127
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 127 (accept_3_3 2 4 127 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 127
  (Polychromatic418967fa.accept_10_1_4_7_1_374 1 4 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 127)))) (allB_succ 3 127 (allA_succ_of_accept 2 3 127 (accept_3_3 2 3 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 127 (Polychromatic418967fa.accept_23_1_3_12_1_6277 1 3 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 127))) (allB_succ 2 127 (allA_of_3_1 2 2 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  127)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


