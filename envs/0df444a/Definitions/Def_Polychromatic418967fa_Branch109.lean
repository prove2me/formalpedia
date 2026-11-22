-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch109
-- name    : Polychromatic418967fa_Branch109
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:10:42.363772+00:00
-- url     : https://prove2.me/theorems/25a68602-f650-4cf0-885c-d1cf86ead950
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

def Polychromatic418967fa.branch_109 : allB 109 109 :=
  allB_succ' 2 108 109 (Eq.refl Bool.true) (allA_succ_of_accept 1 108 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  108 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108 109)) (allB_succ' 3 107 109
  (Eq.refl Bool.true) (allA_of_3_1 3 107 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 106 109 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 109 (accept_3_3 2 106 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 109 (Polychromatic418967fa.accept_24_1_10_13_1_5034 1 106 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 109)))) (allB_succ' 5 105 109 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 105 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 105 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 109 (accept_3_3 2 105 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 109 (Polychromatic418967fa.accept_10_1_5_9_1_157 1
  105 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 109))))) (allB_succ' 6 104 109
  (Eq.refl Bool.true) (allA_of_3_1 6 104 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 103 109 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 103 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 109 (accept_3_3 5 103 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 109 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 103 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 109
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 103 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 109 (accept_3_3 2 103 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 103 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 109))))))) (allB_succ' 8 102 109 (Eq.refl Bool.true) (allA_succ_of_accept 7 102 109
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 102 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 102 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 109 (accept_3_3 5 102 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 102 109 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 102 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  102 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 109 (accept_3_3 2 102
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 109
  (Polychromatic418967fa.accept_10_1_2_9_1_152 1 102 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102 109)))))))) (allB_succ' 9 101 109 (Eq.refl Bool.true) (allA_of_3_1 9 101 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 10 100 109 (Eq.refl Bool.true) (allA_succ_of_accept 9 100 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 109 (accept_3_3 8 100 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 109 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 100 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 100 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 109 (accept_3_3 5 100 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 109 (Polychromatic418967fa.accept_13_4_9_5_1_1641 4 100 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 109 (accept_3_3 2 100 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 100 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100 109)))))))))) (allB_succ' 11 99 109 (Eq.refl Bool.true) (allA_succ_of_accept 10 99 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 99 109 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 99 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 109 (accept_3_3 8 99 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 99 109 (Polychromatic418967fa.accept_19_7_4_14_1_5003 7 99 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 109 (accept_3_3 5 99 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 109
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 99 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 109 (accept_3_3 2 99 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  109 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1 99 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 109))))))))))) (allB_succ' 12 98 109 (Eq.refl Bool.true) (allA_of_3_1 12 98 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 97 109 (Eq.refl Bool.true) (allA_succ_of_accept 12 97 109
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 109 (accept_3_3 11 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 97 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 109 (accept_3_3 8 97 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 109 (Polychromatic418967fa.accept_19_7_2_14_1_3569 7 97 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 109
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 109 (accept_3_3 5 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  109 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 97 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 109 (accept_3_3 2 97 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 109 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 97 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 109))))))))))))) (allB_succ' 14 96 109 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 96 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 96 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 109 (accept_3_3 11 96 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 109 (Polychromatic418967fa.accept_15_10_6_4_1_1256
  10 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 109
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 96 109 (accept_3_3 8 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96
  109 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 96 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 96 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 109 (accept_3_3 5 96 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 96 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 96 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 96
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 109 (accept_3_3 2 96 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 1
  96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 109)))))))))))))) (allB_succ' 15 95
  109 (Eq.refl Bool.true) (allA_of_3_1 15 95 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 94 109 (Eq.refl
  Bool.true) (allA_succ_of_accept 15 94 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 109 (accept_3_3 14 94 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 94 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 109
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 109 (accept_3_3 11 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 109 (Polychromatic418967fa.accept_16_10_14_13_1_1870 10 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 94 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 109 (accept_3_3 8 94 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 109
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 109 (accept_3_3 5 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  109 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 94 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 109 (accept_3_3 2 94 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 94 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 109)))))))))))))))) (allB_succ' 17 93 109 (Eq.refl
  Bool.true) (allA_succ_of_accept 16 93 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 15
  93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 109 (accept_3_3 14 93
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 109
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 93 109 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 109 (accept_3_3 11 93 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 93 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 93 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 109 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9
  93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 109 (accept_3_3 8 93 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 7
  93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 109
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 109 (accept_3_3 5 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 109 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 93 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 109 (accept_3_3 2 93 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 109 (Polychromatic418967fa.accept_15_1_3_4_1_1217 1 93 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 109))))))))))))))))) (allB_succ' 18 92 109 (Eq.refl Bool.true)
  (allA_of_3_1 18 92 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 91 109 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 91 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 109 (accept_3_3 17 91 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 91 109 (Polychromatic418967fa.accept_17_16_6_7_1_2715 16 91 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 109
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 109 (accept_3_3 14 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 109 (Polychromatic418967fa.accept_17_13_6_7_1_4999 13 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 109 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 91 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 109 (accept_3_3 11 91 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 109
  (Polychromatic418967fa.accept_27_9_10_1_1_5033 9 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 109 (accept_3_3 8 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  109 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 91 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 109 (accept_3_3 5 91 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 109 (Polychromatic418967fa.accept_14_4_7_11_1_790 4 91 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 109
  (Polychromatic418967fa.accept_14_3_7_11_1_765 3 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 109 (accept_3_3 2 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  109 (Polychromatic418967fa.accept_19_1_15_14_1_5032 1 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91 109))))))))))))))))))) (allB_succ' 20 90 109 (Eq.refl Bool.true) (allA_succ_of_accept 19 90
  109 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 90 109 (Polychromatic418967fa.accept_21_18_6_4_1_5031 18 90 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 109 (accept_3_3 17 90 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 90 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 90 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 109 (accept_3_3 14 90
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 109
  (Polychromatic418967fa.accept_20_13_10_9_1_5030 13 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 90 109 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 90 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 109 (accept_3_3 11 90 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 90 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 90 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 90 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 90
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 109 (accept_3_3 8 90 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 109
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 109 (accept_3_3 5 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  109 (Polychromatic418967fa.accept_13_4_12_5_1_476 4 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 90 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 109 (accept_3_3 2 90 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 109 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 90 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 109)))))))))))))))))))) (allB_succ' 21 89 109
  (Eq.refl Bool.true) (allA_of_3_1 21 89 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 88 109 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 88 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 109 (accept_3_3 20 88 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 109 (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 88 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 109
  (Polychromatic418967fa.accept_23_18_19_17_1_5029 18 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 88 109 (accept_3_3 17 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 88 109 (Polychromatic418967fa.accept_17_16_3_7_1_5028 16 88 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 109 (accept_3_3 14 88 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 109
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 109 (accept_3_3 11 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 109 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 109 (accept_3_3 8 88 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 109 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 88 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 109
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 109 (accept_3_3 5 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  109 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 109 (accept_3_3 2 88 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 109 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 88 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 109)))))))))))))))))))))) (allB_succ' 23 87 109 (Eq.refl
  Bool.true) (allA_succ_of_accept 22 87 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 21
  87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 109 (accept_3_3 20 87
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 109
  (Polychromatic418967fa.accept_23_19_18_17_1_5027 19 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 109 (accept_3_3 17 87 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 109
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 109 (accept_3_3 14 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 87 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 109 (accept_3_3 11 87 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 109
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 109 (accept_3_3 8 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  109 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 109 (accept_3_3 5 87 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 87
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 109 (accept_3_3 2 87 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 109)))))))))))))))))))))))
  (allB_succ' 24 86 109 (Eq.refl Bool.true) (allA_of_3_1 24 86 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  25 85 109 (Eq.refl Bool.true) (allA_succ_of_accept 24 85 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 85 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 109 (accept_3_3 23 85 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 109 (Polychromatic418967fa.accept_15_7_10_4_1_151
  22 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 109
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 109 (accept_3_3 20 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 109 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 109 (Polychromatic418967fa.accept_14_4_1_11_1_5026 18 85 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 109 (accept_3_3 17 85 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 85 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 109
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 109 (accept_3_3 14 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 109 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 109 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 85 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 109 (accept_3_3 11 85 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 85 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 109
  (Polychromatic418967fa.accept_11_9_8_10_1_934 9 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 109 (accept_3_3 8 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  109 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 85 109 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 85 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 109 (accept_3_3 5 85 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 85 109 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 85 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 109 (accept_3_3 2 85 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 109 (Polychromatic418967fa.accept_10_1_5_9_1_157 1
  85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 109)))))))))))))))))))))))))
  (allB_succ' 26 84 109 (Eq.refl Bool.true) (allA_succ_of_accept 25 84 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 25
  84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 109
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 109 (accept_3_3 23 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 109 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 109 (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 84 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 109 (accept_3_3 20 84 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 109 (Polychromatic418967fa.accept_20_19_4_9_1_5025 19 84 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 109
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 109 (accept_3_3 17 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 84 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 109 (accept_3_3 14 84 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 109 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 84 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 109
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 109 (accept_3_3 11 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 109 (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 84 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 109 (accept_3_3 8 84 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 84 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 109
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 109 (accept_3_3 5 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  109 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 84 109 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 84 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 109 (accept_3_3 2 84 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 84 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 109)))))))))))))))))))))))))) (allB_succ' 27 83 109 (Eq.refl
  Bool.true) (allA_of_3_1 27 83 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 82 109 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 82 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 109 (accept_3_3 26 82 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 82 109 (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 82 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 109
  (Polychromatic418967fa.accept_19_5_6_14_1_5010 24 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 109 (accept_3_3 23 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 82 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 109 (accept_3_3 20 82 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 109
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 109 (accept_3_3 17 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 109 (accept_3_3 14 82 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 82 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 109
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 109 (accept_3_3 11 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 109 (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 82 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 109 (accept_3_3 8 82 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 109
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 109 (accept_3_3 5 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  109 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 82 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 109 (accept_3_3 2 82 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 82 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 109)))))))))))))))))))))))))))) (allB_succ' 29 81 109
  (Eq.refl Bool.true) (allA_succ_of_accept 28 81 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 109
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 109 (accept_3_3 26 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 109 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 109 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 109 (accept_3_3 23 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 81 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 109
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 109 (accept_3_3 20 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 109 (Polychromatic418967fa.accept_13_6_3_5_1_3167 19 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 109 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 109 (accept_3_3 17 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 109
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 109 (accept_3_3 14 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 109 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 109 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 109 (accept_3_3 11 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 81 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 109
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 109 (accept_3_3 8 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  109 (Polychromatic418967fa.accept_21_7_18_4_1_5024 7 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 109 (Polychromatic418967fa.accept_13_6_3_5_1_3167 6 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 109 (accept_3_3 5 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 109
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 109 (accept_3_3 2 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  109 (Polychromatic418967fa.accept_13_1_3_5_1_140 1 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 109))))))))))))))))))))))))))))) (allB_succ' 30 80 109 (Eq.refl Bool.true) (allA_of_3_1 30 80 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 79 109 (Eq.refl Bool.true) (allA_succ_of_accept 30 79 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 109 (accept_3_3 29 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 109 (Polychromatic418967fa.accept_16_12_15_13_1_3872 28 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 109 (accept_3_3 26 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 109 (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 79 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 109
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 109 (accept_3_3 23 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 109 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 109 (accept_3_3 20 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 109 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 79 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 109 (accept_3_3 17 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 109 (Polychromatic418967fa.accept_13_3_1_5_1_499 16 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 109 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 109 (accept_3_3 14 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 79 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 109
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 109 (accept_3_3 11 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 109 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 109 (accept_3_3 8 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 109 (Polychromatic418967fa.accept_19_7_3_14_1_5023 7 79 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 109 (accept_3_3 5 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  109 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 109 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 79 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 109 (accept_3_3 2 79 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 109 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 109))))))))))))))))))))))))))))))) (allB_succ' 32 78 109
  (Eq.refl Bool.true) (allA_succ_of_accept 31 78 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 109
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 109 (accept_3_3 29 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 109 (Polychromatic418967fa.accept_32_28_14_13_1_5022 28 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 109 (accept_3_3 26 78 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 78 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 109
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 109 (accept_3_3 23 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 78 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 109 (accept_3_3 20 78 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 109
  (Polychromatic418967fa.accept_14_4_8_11_1_794 18 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 109 (accept_3_3 17 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 109 (accept_3_3 14 78 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 78 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 109
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 109 (accept_3_3 11 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 109 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 78 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 109 (accept_3_3 8 78 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 109
  (Polychromatic418967fa.accept_21_6_15_4_1_5021 6 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 109 (accept_3_3 5 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  109 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 109 (accept_3_3 2 78 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 109 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 78 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 109)))))))))))))))))))))))))))))))) (allB_succ' 33 77 109
  (Eq.refl Bool.true) (allA_of_3_1 33 77 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 76 109 (Eq.refl
  Bool.true) (allA_succ_of_accept 33 76 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 109 (accept_3_3 32 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 76 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 109
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 109 (accept_3_3 29 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 109 (Polychromatic418967fa.accept_21_7_13_4_1_2169 28 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 109 (accept_3_3 26 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 76 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 109
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 109 (accept_3_3 23 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 109 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 109 (accept_3_3 20 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 109 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 76 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 109
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 109 (accept_3_3 17 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 109 (accept_3_3 14 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 109 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 76 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 109
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 109 (accept_3_3 11 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 109 (accept_3_3 8 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 76 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 109
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 109 (accept_3_3 5 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  109 (Polychromatic418967fa.accept_16_4_12_13_1_990 4 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 76 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 109 (accept_3_3 2 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 76 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 109)))))))))))))))))))))))))))))))))) (allB_succ' 35
  75 109 (Eq.refl Bool.true) (allA_succ_of_accept 34 75 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 109
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 109 (accept_3_3 32 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 109 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 109 (accept_3_3 29 75 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 109
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 109 (accept_3_3 26 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 75 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 109 (accept_3_3 23 75 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 109
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 109 (accept_3_3 20 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 109 (Polychromatic418967fa.accept_11_8_9_10_1_503 19 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 109 (accept_3_3 17 75 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 109
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 109 (accept_3_3 14 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 109 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 75 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 109 (accept_3_3 11 75 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 109
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 109 (accept_3_3 8 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  109 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 109 (accept_3_3 5 75 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 109 (Polychromatic418967fa.accept_19_3_18_14_1_5020
  3 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 109 (accept_3_3 2 75
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 109 (Polychromatic418967fa.accept_7_1_5_4_1_134
  1 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  109))))))))))))))))))))))))))))))))))) (allB_succ' 36 74 109 (Eq.refl Bool.true) (allA_of_3_1 36 74 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 73 109 (Eq.refl Bool.true) (allA_succ_of_accept 36 73 109
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 109 (accept_3_3 35 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 109 (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 73 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 109 (accept_3_3 32 73 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 109 (Polychromatic418967fa.accept_19_12_16_14_1_3661 31 73
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 109
  (Polychromatic418967fa.accept_19_11_16_14_1_3553 30 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 73 109 (accept_3_3 29 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 73 109 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 73 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 73 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 109 (accept_3_3 26 73 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 109 (Polychromatic418967fa.accept_11_3_7_10_1_180
  25 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 109
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 109 (accept_3_3 23 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 109 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 73 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 109 (accept_3_3 20 73 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 109 (Polychromatic418967fa.accept_20_19_13_9_1_5019 19 73
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 109
  (Polychromatic418967fa.accept_19_18_16_14_1_2377 18 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 73 109 (accept_3_3 17 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 73 109 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 73 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 73 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 109 (accept_3_3 14 73 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 109
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 109 (accept_3_3 11 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 109 (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 109 (Polychromatic418967fa.accept_15_9_13_4_1_1209 9 73 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 109 (accept_3_3 8 73 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 109 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 73 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 109
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 109 (accept_3_3 5 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  109 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 109 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 73 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 109 (accept_3_3 2 73 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 73 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 109))))))))))))))))))))))))))))))))))))) (allB_succ' 38 72 109
  (Eq.refl Bool.true) (allA_succ_of_accept 37 72 109 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 72 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 109
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 109 (accept_3_3 35 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 109 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 109 (accept_3_3 32 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 109 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 72 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 109
  (Polychromatic418967fa.accept_19_11_15_14_1_5018 30 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 72 109 (accept_3_3 29 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 109 (Polychromatic418967fa.accept_13_2_7_5_1_3189 28 72 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 72 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 109 (accept_3_3 26 72 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 109 (Polychromatic418967fa.accept_13_12_7_5_1_3147
  25 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 109
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 109 (accept_3_3 23 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 109 (Polychromatic418967fa.accept_15_7_12_4_1_1236 22 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 109 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 109 (accept_3_3 20 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 109 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 72 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 109
  (Polychromatic418967fa.accept_19_18_15_14_1_5017 18 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 72 109 (accept_3_3 17 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 109 (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 72 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 72 109 (Polychromatic418967fa.accept_13_2_7_5_1_3189 15 72 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 109 (accept_3_3 14 72 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 13
  72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 109
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 109 (accept_3_3 11 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 109 (Polychromatic418967fa.accept_19_10_15_14_1_5016 10 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 109 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 109 (accept_3_3 8 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 109 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 72 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 109
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 109 (accept_3_3 5 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  109 (Polychromatic418967fa.accept_16_4_8_13_1_1059 4 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 72 109 (Polychromatic418967fa.accept_16_3_8_13_1_3867 3 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 109 (accept_3_3 2 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 109 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 72 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 109)))))))))))))))))))))))))))))))))))))) (allB_succ'
  39 71 109 (Eq.refl Bool.true) (allA_of_3_1 39 71 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 70 109
  (Eq.refl Bool.true) (allA_succ_of_accept 39 70 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 109 (accept_3_3 38 70 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 109 (Polychromatic418967fa.accept_15_7_10_4_1_151 37 70 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 109
  (Polychromatic418967fa.accept_15_6_10_4_1_150 36 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 70 109 (accept_3_3 35 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  70 109 (Polychromatic418967fa.accept_19_15_13_14_1_5015 34 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 70 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 109 (accept_3_3 32 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 109
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 109 (accept_3_3 29 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  70 109 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 70 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 109 (accept_3_3 26 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 109 (Polychromatic418967fa.accept_16_9_6_13_1_3831 25 70 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 109
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 109 (accept_3_3 23 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 109 (accept_3_3 20 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 109
  (Polychromatic418967fa.accept_19_18_13_14_1_4995 18 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 70 109 (accept_3_3 17 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 70 109 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 70 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 109 (accept_3_3 14 70 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 109
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 109 (accept_3_3 11 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  70 109 (Polychromatic418967fa.accept_18_10_16_1_1_1534 10 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 109 (accept_3_3 8 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 109
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 70 109 (accept_3_3 5 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70
  109 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 70 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 109 (accept_3_3 2 70 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 70 109 (Polychromatic418967fa.accept_19_1_13_14_1_3509 1 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 109)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 69
  109 (Eq.refl Bool.true) (allA_succ_of_accept 40 69 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 109
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 109 (accept_3_3 38 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 109 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 69 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 109 (accept_3_3 35 69 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 69 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 109
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 109 (accept_3_3 32 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 69 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 109 (accept_3_3 29 69 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 109
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 109 (accept_3_3 26 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 109 (accept_3_3 23 69 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 69 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 109
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 109 (accept_3_3 20 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 109 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 109 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 69 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 109 (accept_3_3 17 69 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 109
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 109 (accept_3_3 14 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 109 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 109 (accept_3_3 11 69 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 109
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 109 (accept_3_3 8 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  109 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 109 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 69 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 109 (accept_3_3 5 69 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 109 (accept_3_3 2 69 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 109 (Polychromatic418967fa.accept_13_1_4_5_1_113 1
  69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  109))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 68 109 (Eq.refl Bool.true) (allA_of_3_1 42 68 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 67 109 (Eq.refl Bool.true) (allA_succ_of_accept 42 67 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 109 (accept_3_3 41 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 109 (Polychromatic418967fa.accept_15_10_7_4_1_1222 40 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 109 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 109 (accept_3_3 38 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 109 (Polychromatic418967fa.accept_17_3_16_7_1_5014 37 67 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 109
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 109 (accept_3_3 35 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 109 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 109 (accept_3_3 32 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 109 (Polychromatic418967fa.accept_11_9_1_10_1_920 31 67 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 109 (accept_3_3 29 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 109 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 109 (Polychromatic418967fa.accept_15_12_7_4_1_2921 27 67 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 109 (accept_3_3 26 67 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 67 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 109
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 109 (accept_3_3 23 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 109 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 109 (accept_3_3 20 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 109 (Polychromatic418967fa.accept_23_19_21_17_1_4957 19 67 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 109 (accept_3_3 17 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 109 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 109 (accept_3_3 14 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 109 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 67 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 109
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 109 (accept_3_3 11 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 109 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 109 (accept_3_3 8 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 109 (accept_3_3 5 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  109 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 109 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 109 (accept_3_3 2 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 109 (Polychromatic418967fa.accept_16_1_3_13_1_2785 1 67 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 109)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 66 109 (Eq.refl Bool.true) (allA_succ_of_accept 43 66 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 109
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 66 109 (accept_3_3 41 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  66 109 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 66 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 109 (accept_3_3 38 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 109 (Polychromatic418967fa.accept_16_5_2_13_1_1007 37 66 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 109
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 109 (accept_3_3 35 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  66 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 66 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 109 (accept_3_3 32 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 109
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 30 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 66 109 (accept_3_3 29 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  66 109 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 66 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 109 (accept_3_3 26 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 66 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 109
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 66 109 (accept_3_3 23 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  66 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 66 109 (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 109 (accept_3_3 20 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 109
  (Polychromatic418967fa.accept_21_18_3_4_1_5013 18 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 109 (accept_3_3 17 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  66 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 109 (accept_3_3 14 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 66 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 109
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 66 109 (accept_3_3 11 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  66 109 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 66 109 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 109 (accept_3_3 8 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 109
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 109 (accept_3_3 5 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66
  109 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 66 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 109 (accept_3_3 2 66 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 66 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 109)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  65 109 (Eq.refl Bool.true) (allA_of_3_1 45 65 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 64 109
  (Eq.refl Bool.true) (allA_succ_of_accept 45 64 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 109 (accept_3_3 44 64 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 64 109 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 64 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 109
  (Polychromatic418967fa.accept_19_4_7_14_1_3537 42 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 64 109 (accept_3_3 41 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  64 109 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 64 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 109 (accept_3_3 38 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 64 109 (Polychromatic418967fa.accept_19_18_7_14_1_5012 37 64 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 109
  (Polychromatic418967fa.accept_17_2_13_7_1_5011 36 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 64 109 (accept_3_3 35 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  64 109 (Polychromatic418967fa.accept_11_1_9_10_1_184 34 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 64 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 109 (accept_3_3 32 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 64 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 64 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 109
  (Polychromatic418967fa.accept_11_8_9_10_1_503 30 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 64 109 (accept_3_3 29 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  64 109 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 64 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 109 (accept_3_3 26 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 64 109 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 64 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 109
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 64 109 (accept_3_3 23 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  64 109 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 64 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 109 (accept_3_3 20 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 109 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 64 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 109
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 109 (accept_3_3 17 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  64 109 (Polychromatic418967fa.accept_18_16_10_1_1_3696 16 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 109 (accept_3_3 14 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 109 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 64 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 109
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 109 (accept_3_3 11 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 109 (accept_3_3 8 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 109 (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 64 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 109
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 109 (accept_3_3 5 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  109 (Polychromatic418967fa.accept_13_4_12_5_1_476 4 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 64 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 109 (accept_3_3 2 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 109 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 64 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64 109))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 63 109 (Eq.refl Bool.true) (allA_succ_of_accept 46 63 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 109
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 109 (accept_3_3 44 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 109 (Polychromatic418967fa.accept_19_5_6_14_1_5010 43 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 109 (accept_3_3 41 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 109
  (Polychromatic418967fa.accept_17_5_12_7_1_2651 39 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 109 (accept_3_3 38 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 109 (Polychromatic418967fa.accept_15_7_3_4_1_574 37 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 109 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 109 (accept_3_3 35 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 109
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 109 (accept_3_3 32 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 109 (Polychromatic418967fa.accept_11_9_8_10_1_934 31 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 109 (accept_3_3 29 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 109
  (Polychromatic418967fa.accept_19_8_6_14_1_5009 27 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 109 (accept_3_3 26 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 109 (Polychromatic418967fa.accept_26_25_11_5_1_5008 25 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 109 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 109 (accept_3_3 23 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 109
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 109 (accept_3_3 20 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 109 (Polychromatic418967fa.accept_13_6_11_5_1_133 19 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 109 (accept_3_3 17 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 109
  (Polychromatic418967fa.accept_20_15_3_9_1_5007 15 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 109 (accept_3_3 14 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 109 (Polychromatic418967fa.accept_22_13_19_21_1_5006 13 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 109 (Polychromatic418967fa.accept_16_12_15_13_1_3872 12 63 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 109 (accept_3_3 11 63 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 109
  (Polychromatic418967fa.accept_11_9_8_10_1_934 9 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 109 (accept_3_3 8 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  109 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 109 (accept_3_3 5 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 109
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 109 (accept_3_3 2 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  109 (Polychromatic418967fa.accept_15_1_3_4_1_1217 1 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 109))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 62 109 (Eq.refl Bool.true)
  (allA_of_3_1 48 62 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 61 109 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 61 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 61 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 61 109 (accept_3_3 47 61 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 61 109 (Polychromatic418967fa.accept_19_8_4_14_1_5005 46 61 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 61 109
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 61 109 (accept_3_3 44 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  61 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 61 109 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 61 109 (accept_3_3 41 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 61 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 109
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 61 109 (accept_3_3 38 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  61 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 61 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 61 109 (accept_3_3 35 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 61 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 61 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 61 109
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 61 109 (accept_3_3 32 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  61 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 61 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 61 109 (accept_3_3 29 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 61 109 (Polychromatic418967fa.accept_10_8_1_9_1_413 28 61 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 109
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 61 109 (accept_3_3 26 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  61 109 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 61 109 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 109 (accept_3_3 23 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 61 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 61 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 109
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 61 109 (accept_3_3 20 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  61 109 (Polychromatic418967fa.accept_22_19_17_21_1_5004 19 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 61 109 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 109 (accept_3_3 17 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 61 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 61 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 109
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 61 109 (accept_3_3 14 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  61 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 61 109 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 109 (accept_3_3 11 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 61 109 (Polychromatic418967fa.accept_19_10_4_14_1_4981 10 61 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 109
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 61 109 (accept_3_3 8 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61
  109 (Polychromatic418967fa.accept_19_7_4_14_1_5003 7 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 61 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 109 (accept_3_3 5 61 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 61 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 109
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 61 109 (accept_3_3 2 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61
  109 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 61 109))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 60 109 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 60 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 109 (accept_3_3 47 60 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 109 (Polychromatic418967fa.accept_19_8_3_14_1_3571
  46 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 60 109
  (Polychromatic418967fa.accept_18_9_6_1_1_3687 45 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 60 109 (accept_3_3 44 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  60 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 60 109 (Polychromatic418967fa.accept_13_3_8_5_1_974 42 60 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 109 (accept_3_3 41 60 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 60 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 60 109
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 60 109 (accept_3_3 38 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  60 109 (Polychromatic418967fa.accept_11_4_5_10_1_926 37 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 60 109 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 60 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 109 (accept_3_3 35 60 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 60 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 109
  (Polychromatic418967fa.accept_8_1_4_5_1_48 33 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 60 109 (accept_3_3 32 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  60 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 60 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 60 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 109 (accept_3_3 29 60 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 109 (Polychromatic418967fa.accept_11_6_5_10_1_2724 28 60 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 109
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 60 109 (accept_3_3 26 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  60 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 60 109 (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 60 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 109 (accept_3_3 23 60 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 60 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 109
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 60 109 (accept_3_3 20 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  60 109 (Polychromatic418967fa.accept_17_2_9_7_1_5002 19 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 60 109 (Polychromatic418967fa.accept_19_18_3_14_1_5001 18 60 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 109 (accept_3_3 17 60 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 60 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 60 109
  (Polychromatic418967fa.accept_11_4_5_10_1_926 15 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 60 109 (accept_3_3 14 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  60 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 60 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 60 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 109 (accept_3_3 11 60 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 109 (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 60 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 60 109
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 60 109 (accept_3_3 8 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60
  109 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 60 109 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 60 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 109 (accept_3_3 5 60 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 60 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 60 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 60
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 109 (accept_3_3 2 60 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 60
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  109)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 59 109 (Eq.refl Bool.true) (allA_of_3_1 51 59 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 58 109 (Eq.refl Bool.true) (allA_succ_of_accept 51 58 109
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 109 (accept_3_3 50 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 109 (Polychromatic418967fa.accept_13_10_6_5_1_2297 49 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 58 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 109 (accept_3_3 47 58 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 109 (Polychromatic418967fa.accept_16_14_10_13_1_2768 46 58 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 109 (accept_3_3 44 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 109 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 58 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 109 (accept_3_3 41 58 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 109 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 58 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 109
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 109 (accept_3_3 38 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 109 (Polychromatic418967fa.accept_10_7_8_9_1_785 37 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 109 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 58 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 109 (accept_3_3 35 58 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 58 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 109 (accept_3_3 32 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 109 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 58 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 109 (accept_3_3 29 58 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 109 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 58 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 109
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 109 (accept_3_3 26 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 109 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 58 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 109 (accept_3_3 23 58 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 109 (Polychromatic418967fa.accept_23_22_12_17_1_5000 22 58 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 109 (accept_3_3 20 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 109 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 58 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 109 (accept_3_3 17 58 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 58 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 109
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 109 (accept_3_3 14 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 109 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 58 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 109 (accept_3_3 11 58 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 109 (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 58 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 109 (accept_3_3 8 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 58 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 109 (accept_3_3 5 58 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 109 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 58 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 109 (accept_3_3 2 58 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 109 (Polychromatic418967fa.accept_10_1_8_9_1_787 1
  58 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  109)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 57 109 (Eq.refl Bool.true) (allA_succ_of_accept
  52 57 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 57 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 109 (accept_3_3 50 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 109 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 57 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 109
  (Polychromatic418967fa.accept_10_8_7_9_1_425 48 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 109 (accept_3_3 47 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 109 (accept_3_3 44 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 57 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 109
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 109 (accept_3_3 41 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 109 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 109 (accept_3_3 38 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 109 (Polychromatic418967fa.accept_15_7_12_4_1_1236 37 57 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 109
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 109 (accept_3_3 35 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 109 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 109 (accept_3_3 32 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 57 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 109
  (Polychromatic418967fa.accept_17_13_6_7_1_4999 30 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 109 (accept_3_3 29 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 109 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 109 (accept_3_3 26 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 57 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 109
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 109 (accept_3_3 23 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 109 (Polychromatic418967fa.accept_16_5_9_13_1_3845 21 57 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 109 (accept_3_3 20 57 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 109 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 57 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 109
  (Polychromatic418967fa.accept_10_8_7_9_1_425 18 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 109 (accept_3_3 17 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 109 (accept_3_3 14 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 109 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 57 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 109
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 109 (accept_3_3 11 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 109 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 109 (accept_3_3 8 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 57 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 109
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 109 (accept_3_3 5 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 109 (accept_3_3 2 57 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 109 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 57 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 109)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 54 56 109 (Eq.refl Bool.true) (allA_of_3_1 54 56 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  55 109 (allA_succ_of_accept 54 55 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 109 (accept_3_3 53 55 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 51
  55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 109 (accept_3_3 50 55
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 109
  (Polychromatic418967fa.accept_19_11_17_14_1_4998 49 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 109 (Polychromatic418967fa.accept_13_9_3_5_1_1605 48 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 109 (accept_3_3 47 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 109
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 109 (accept_3_3 44 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 109 (Polychromatic418967fa.accept_15_13_10_4_1_1232 43 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 109 (accept_3_3 41 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 109 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 55 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 109
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 39 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 109 (accept_3_3 38 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 109 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 109 (accept_3_3 35 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 109
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 109 (accept_3_3 32 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 109 (accept_3_3 29 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 109 (Polychromatic418967fa.accept_13_2_3_5_1_2294 28 55 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 109
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 109 (accept_3_3 26 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 109 (Polychromatic418967fa.accept_16_9_7_13_1_4997 25 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 109 (accept_3_3 23 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 109
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 109 (accept_3_3 20 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 109 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 109 (accept_3_3 17 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 55 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 109
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 109 (accept_3_3 14 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 109 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 109 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 109 (accept_3_3 11 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 109
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 109 (accept_3_3 8 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  109 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 55 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 109 (accept_3_3 5 55 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 109 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 55 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 109
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 109 (accept_3_3 2 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55
  109 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 55 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 55 109))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 109 (allA_succ_of_accept 53 54
  109 (accept_3_3 53 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 109
  (Polychromatic418967fa.accept_16_4_6_13_1_1874 52 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 54 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 109 (accept_3_3 50 54 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 54 109 (Polychromatic418967fa.accept_13_10_2_5_1_1633 49 54 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 109
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 109 (accept_3_3 47 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 109 (Polychromatic418967fa.accept_13_7_2_5_1_2344 46 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 109 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 109 (accept_3_3 44 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 109
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 42 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 109 (accept_3_3 41 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 109 (Polychromatic418967fa.accept_15_10_9_4_1_2924 40 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 109 (accept_3_3 38 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 54 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 109
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 109 (accept_3_3 35 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 109 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 109 (accept_3_3 32 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 109
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 109 (accept_3_3 29 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 109 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 109 (accept_3_3 26 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 109 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 54 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 109
  (Polychromatic418967fa.accept_19_5_16_14_1_2374 24 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 109 (accept_3_3 23 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 109 (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 109 (accept_3_3 20 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 109
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 109 (accept_3_3 17 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 109 (accept_3_3 14 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 54 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 109
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 109 (accept_3_3 11 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 109 (Polychromatic418967fa.accept_13_10_2_5_1_1633 10 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 109 (accept_3_3 8 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 109
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 109 (accept_3_3 5 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  109 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 54 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 109 (accept_3_3 2 54 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 54 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  109)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 109 (allA_of_3_1 53 53 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 109 (allA_succ_of_accept 51 52 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 109 (accept_3_3 50 52 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 49
  52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 109
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 109 (accept_3_3 47 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 109 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 109 (accept_3_3 44 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 52 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 109
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 109 (accept_3_3 41 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 109 (accept_3_3 38 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 109 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 52 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 109
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 109 (accept_3_3 35 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 109 (accept_3_3 32 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 52 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 109
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 109 (accept_3_3 29 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 109 (Polychromatic418967fa.accept_16_12_4_13_1_3827 28 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 109 (accept_3_3 26 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 52 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 109
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 109 (accept_3_3 23 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 109 (accept_3_3 20 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 109 (Polychromatic418967fa.accept_20_19_12_9_1_4996 19 52 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 109
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 109 (accept_3_3 17 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 109 (Polychromatic418967fa.accept_21_16_10_4_1_3433 16 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 109 (accept_3_3 14 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 52 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 109
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 109 (accept_3_3 11 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 109 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 109 (accept_3_3 8 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 109 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 52 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 109
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 109 (accept_3_3 5 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  109 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 52 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 109 (accept_3_3 2 52 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 52 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 109))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 109 (allA_succ_of_accept 50 51 109 (accept_3_3 50 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 51 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 109 (accept_3_3 47 51 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 109
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 109 (accept_3_3 44 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 109 (accept_3_3 41 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 109
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 109 (accept_3_3 38 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 109 (Polychromatic418967fa.accept_19_18_13_14_1_4995 37 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 109 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 109 (accept_3_3 35 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 109
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 109 (accept_3_3 32 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 109 (accept_3_3 29 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 109
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 109 (accept_3_3 26 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 109 (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 109 (accept_3_3 23 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 109
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 109 (accept_3_3 20 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 109 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 109 (accept_3_3 17 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 109
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 109 (accept_3_3 14 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 109 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 109 (accept_3_3 11 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 109
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 109 (accept_3_3 8 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  109 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 109 (accept_3_3 5 51 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 51
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 109 (accept_3_3 2 51 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 109 (Polychromatic418967fa.accept_13_1_12_5_1_1601
  1 51 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  109))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 109 (allA_of_3_1 50 50 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 109 (allA_succ_of_accept 48 49 109 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 109 (accept_3_3 47 49 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 109 (Polychromatic418967fa.accept_14_4_7_11_1_790
  46 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 109
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 109 (accept_3_3 44 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 109 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 109 (accept_3_3 41 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 109 (Polychromatic418967fa.accept_21_19_7_4_1_4994 40 49 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 109
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 109 (accept_3_3 38 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 109 (Polychromatic418967fa.accept_11_4_5_10_1_926 37 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 109 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 109 (accept_3_3 35 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 49 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 109
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 109 (accept_3_3 32 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 109 (Polychromatic418967fa.accept_14_3_7_11_1_765 31 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 109 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 109 (accept_3_3 29 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 109 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 49 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 109
  (Polychromatic418967fa.accept_21_6_7_4_1_4993 27 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 109 (accept_3_3 26 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 109 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 109 (accept_3_3 23 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 109 (Polychromatic418967fa.accept_17_5_15_7_1_4992 22 49 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 109
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 109 (accept_3_3 20 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 109 (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 109 (Polychromatic418967fa.accept_14_4_7_11_1_790 18 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 109 (accept_3_3 17 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 109
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 109 (accept_3_3 14 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 109 (Polychromatic418967fa.accept_21_13_7_4_1_4991 13 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 109 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 109 (accept_3_3 11 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 109 (Polychromatic418967fa.accept_14_10_7_11_1_3015 10 49 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 109
  (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 109 (accept_3_3 8 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  109 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 109 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 49 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 109 (accept_3_3 5 49 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 109 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 49 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 109 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 49
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 109 (accept_3_3 2 49 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 109 (Polychromatic418967fa.accept_21_1_7_4_1_4947 1
  49 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  109))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 109 (allA_succ_of_accept 47 48 109 (accept_3_3 47
  48 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 109
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 46 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 109 (accept_3_3 44 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 48 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 42
  48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 109 (accept_3_3 41 48
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 109
  (Polychromatic418967fa.accept_7_5_6_4_1_117 40 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 48 109 (Polychromatic418967fa.accept_18_3_12_1_1_3787 39 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 109 (accept_3_3 38 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 48 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 48 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 109 (Polychromatic418967fa.accept_21_15_6_4_1_4990
  36 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 109 (accept_3_3 35
  48 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 109
  (Polychromatic418967fa.accept_9_7_3_1_1_386 34 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 48 109 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 109 (accept_3_3 32 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 48 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 30
  48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 109 (accept_3_3 29 48
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 109
  (Polychromatic418967fa.accept_13_2_9_5_1_959 28 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 48 109 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 109 (accept_3_3 26 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 48 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 48 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 24
  48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 109 (accept_3_3 23 48
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 109
  (Polychromatic418967fa.accept_9_4_3_1_1_154 22 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 48 109 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 109 (accept_3_3 20 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 48 109 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 48 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 109
  (Polychromatic418967fa.accept_19_18_10_14_1_2392 18 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 48 109 (accept_3_3 17 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 48 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 109 (accept_3_3 14 48 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 109 (Polychromatic418967fa.accept_9_4_3_1_1_154 13
  48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 109
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 109 (accept_3_3 11 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 109 (accept_3_3 8 48 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 109
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 109 (accept_3_3 5 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  109 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 48 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 109 (accept_3_3 2 48 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 109 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 48 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 109)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 109 (allA_of_3_1 47 47 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 109 (allA_succ_of_accept 45 46
  109 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 109 (accept_3_3 44 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 109 (Polychromatic418967fa.accept_15_12_1_4_1_2899 42 46 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 109 (accept_3_3 41 46 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 109 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 46 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 109
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 109 (accept_3_3 38 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 109 (Polychromatic418967fa.accept_13_11_7_5_1_2314 37 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 109 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 46 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 109 (accept_3_3 35 46 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 109 (Polychromatic418967fa.accept_11_1_2_10_1_1426 34 46
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 109 (accept_3_3 32 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 109 (Polychromatic418967fa.accept_20_10_6_9_1_4989 30 46 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 109 (accept_3_3 29 46 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 109 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 46 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 109
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 109 (accept_3_3 26 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 109 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 109 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 46 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 109 (accept_3_3 23 46 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 109 (Polychromatic418967fa.accept_14_8_4_11_1_3035 22 46
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 109 (accept_3_3 20 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 109 (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 46 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 109 (accept_3_3 17 46 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 109 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 46 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 109
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 109 (accept_3_3 14 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 109 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 109 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 46 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 109 (accept_3_3 11 46 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 109 (Polychromatic418967fa.accept_16_10_14_13_1_1870 10 46
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 109 (accept_3_3 8 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 109 (Polychromatic418967fa.accept_19_6_8_14_1_2351 6 46 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 109 (accept_3_3 5 46 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 109 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 46 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 109 (accept_3_3 2 46 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 109 (Polychromatic418967fa.accept_11_1_2_10_1_1426
  1 46 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  109)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 109 (allA_succ_of_accept 44 45 109 (accept_3_3 44 45
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 109
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 109 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 109 (accept_3_3 41 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 109 (Polychromatic418967fa.accept_12_3_9_1_1_290
  39 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 109 (accept_3_3 38
  45 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 109
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 37 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 45 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 109 (accept_3_3 35 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 45 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 109 (Polychromatic418967fa.accept_21_12_3_4_1_4988
  33 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 109 (accept_3_3 32
  45 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 109
  (Polychromatic418967fa.accept_10_1_5_9_1_157 31 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 45 109 (Polychromatic418967fa.accept_13_4_6_5_1_2333 30 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 109 (accept_3_3 29 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 45 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 27
  45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 109 (accept_3_3 26 45
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 109
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 25 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 45 109 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 109 (accept_3_3 23 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 45 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 45 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 109 (Polychromatic418967fa.accept_10_1_5_9_1_157
  21 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 109 (accept_3_3 20
  45 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 109
  (Polychromatic418967fa.accept_27_19_18_1_1_4987 19 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 109 (Polychromatic418967fa.accept_17_1_11_7_1_4962 18 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 109 (accept_3_3 17 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 45 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 109 (accept_3_3 14 45
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 109
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 109 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 109 (accept_3_3 11 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 45 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 45 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 109 (Polychromatic418967fa.accept_11_9_1_10_1_920 9
  45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 109 (accept_3_3 8 45 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 109 (Polychromatic418967fa.accept_14_7_3_11_1_2199
  7 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 109
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 109 (accept_3_3 5 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 109 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 109 (accept_3_3 2 45 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 45 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 109))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  109 (allA_of_3_1 44 44 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 109 (allA_succ_of_accept 42 43 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 109 (accept_3_3 41 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 109 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 109 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 109 (accept_3_3 38 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 109 (Polychromatic418967fa.accept_23_14_20_17_1_4986 37 43 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 109
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 109 (accept_3_3 35 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 109 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 109 (accept_3_3 32 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 109 (accept_3_3 29 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 109 (Polychromatic418967fa.accept_13_2_4_5_1_3152 28 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 109 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 109 (accept_3_3 26 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 109 (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 43 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 109
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 109 (accept_3_3 23 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 109 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 109 (accept_3_3 20 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 109 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 109 (accept_3_3 17 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 109 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 109 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 109 (accept_3_3 14 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 43 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 109
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 109 (accept_3_3 11 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 109 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 109 (accept_3_3 8 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 109 (Polychromatic418967fa.accept_21_7_1_4_1_4985 7 43 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 109 (accept_3_3 5 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  109 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 43 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 43 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 109 (accept_3_3 2 43 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 109 (Polychromatic418967fa.accept_13_1_4_5_1_113 1 43 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 109))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 109
  (allA_succ_of_accept 41 42 109 (accept_3_3 41 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 109 (accept_3_3 38 42 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 109 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 42 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 109
  (Polychromatic418967fa.accept_23_13_19_17_1_4984 36 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 42 109 (accept_3_3 35 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 42 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 109 (Polychromatic418967fa.accept_17_16_8_7_1_4983 33 42
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 109 (accept_3_3 32 42 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 109
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 109 (accept_3_3 29 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 109 (Polychromatic418967fa.accept_13_2_3_5_1_2294 28 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 109 (accept_3_3 26 42 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 42 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 109
  (Polychromatic418967fa.accept_13_11_3_5_1_982 24 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 109 (accept_3_3 23 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 42 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 109 (accept_3_3 20 42 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 109
  (Polychromatic418967fa.accept_17_1_8_7_1_4982 18 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 109 (accept_3_3 17 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 109 (accept_3_3 14 42 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 42 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 109
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 109 (accept_3_3 11 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 109 (Polychromatic418967fa.accept_19_10_4_14_1_4981 10 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 109 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 42 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 109 (accept_3_3 8 42 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 109
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 6 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 109 (accept_3_3 5 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  109 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 42 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 109 (accept_3_3 2 42 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 109 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 42 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 109)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 109
  (allA_of_3_1 41 41 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 109 (allA_succ_of_accept 39 40 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 109 (accept_3_3 38 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 40 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 109 (accept_3_3 35 40 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 40 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 109 (accept_3_3 32 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 109 (Polychromatic418967fa.accept_17_14_6_7_1_4980 31 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 40 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 109 (accept_3_3 29 40 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 109 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 40 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 109 (accept_3_3 26 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 109 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 40 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 109 (accept_3_3 23 40 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 40 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 109 (accept_3_3 20 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 109 (Polychromatic418967fa.accept_13_6_1_5_1_3988 19 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 109 (Polychromatic418967fa.accept_21_18_19_4_1_4979 18 40 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 109 (accept_3_3 17 40 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 40 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 109 (accept_3_3 14 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 109 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 40 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 109 (accept_3_3 11 40 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 109 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 40 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 109 (accept_3_3 8 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  109 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 40 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 109 (accept_3_3 5 40 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 109 (Polychromatic418967fa.accept_13_4_1_5_1_1628 4 40 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 109 (accept_3_3 2 40 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 1
  40 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  109)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 109 (allA_succ_of_accept 38 39 109 (accept_3_3 38 39 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 109
  (Polychromatic418967fa.accept_19_18_1_14_1_4978 37 39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 109 (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 39 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 109 (accept_3_3 35 39 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 33
  39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 109 (accept_3_3 32 39
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 109
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 39 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 109 (accept_3_3 29 39 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 39 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 109 (Polychromatic418967fa.accept_11_5_6_10_1_1432
  27 39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 109 (accept_3_3 26
  39 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 109
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 39 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 109 (accept_3_3 23 39 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 109 (Polychromatic418967fa.accept_12_9_3_1_1_303
  21 39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 109 (accept_3_3 20
  39 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 109
  (Polychromatic418967fa.accept_21_19_18_4_1_4977 19 39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 39 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 109 (accept_3_3 17 39 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 39 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 15
  39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 109 (accept_3_3 14 39
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 109
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 39 109 (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 39 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 109 (accept_3_3 11 39 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 39 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 109 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 109 (accept_3_3 8 39 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 7
  39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 109 (accept_3_3 5 39 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 109 (Polychromatic418967fa.accept_20_3_19_9_1_4976 3 39 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 109 (accept_3_3 2 39 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 109 (Polychromatic418967fa.accept_21_1_18_4_1_4975 1 39 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 109))))))))))))))))))))))))))))))))))))))) (allB_succ 38 109
  (allA_of_3_1 38 38 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 109 (allA_succ_of_accept 36 37 109
  (Polychromatic418967fa.accept_22_14_15_21_1_4974 36 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 37 109 (accept_3_3 35 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 37 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 37 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 109 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 37 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 109 (accept_3_3 32 37 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 109
  (Polychromatic418967fa.accept_21_10_16_4_1_4973 31 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 109 (Polychromatic418967fa.accept_14_2_9_11_1_3054 30 37 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 109 (accept_3_3 29 37 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 109 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 37 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  37 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 109 (accept_3_3 26 37
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 109
  (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 109 (Polychromatic418967fa.accept_16_8_5_13_1_1021 24 37 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 109 (accept_3_3 23 37 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 109 (Polychromatic418967fa.accept_10_2_7_9_1_783 22 37 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 109 (Polychromatic418967fa.accept_17_4_3_7_1_4971
  21 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 109 (accept_3_3 20
  37 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 109
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 109 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 37 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 109 (accept_3_3 17 37 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 109 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 37 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 109
  (Polychromatic418967fa.accept_19_15_18_14_1_3564 15 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 37 109 (accept_3_3 14 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 37 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 109 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 109 (accept_3_3 11 37 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 109 (Polychromatic418967fa.accept_15_10_7_4_1_1222
  10 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 109
  (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 109 (accept_3_3 8 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  109 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 37 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 37 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 109 (accept_3_3 5 37 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 109 (Polychromatic418967fa.accept_17_4_3_7_1_4971 4 37 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 109
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 109 (accept_3_3 2 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  109 (Polychromatic418967fa.accept_16_1_5_13_1_1025 1 37 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 37 109))))))))))))))))))))))))))))))))))))) (allB_succ 36 109 (allA_succ_of_accept 35 36 109
  (accept_3_3 35 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 109
  (Polychromatic418967fa.accept_13_8_10_5_1_977 34 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 36 109 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 109 (accept_3_3 32 36 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 36 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 36 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 109 (Polychromatic418967fa.accept_13_4_10_5_1_1644
  30 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 109 (accept_3_3 29
  36 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 109
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 28 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 36 109 (Polychromatic418967fa.accept_20_7_16_9_1_4970 27 36 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 109 (accept_3_3 26 36 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 36 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 36 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 24
  36 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 109 (accept_3_3 23 36
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 109
  (Polychromatic418967fa.accept_16_6_4_13_1_3841 22 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 36 109 (Polychromatic418967fa.accept_13_8_10_5_1_977 21 36 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 109 (accept_3_3 20 36 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 36 109 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 109 (Polychromatic418967fa.accept_11_7_3_10_1_1461
  18 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 109 (accept_3_3 17
  36 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 109
  (Polychromatic418967fa.accept_19_16_17_14_1_4969 16 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 109 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 36 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 109 (accept_3_3 14 36 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 109 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 36 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 109
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 109 (accept_3_3 11 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 36 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 109 (accept_3_3 8 36 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 109 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 36 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 109
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 6 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 109 (accept_3_3 5 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  109 (Polychromatic418967fa.accept_13_4_10_5_1_1644 4 36 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 109 (accept_3_3 2 36 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 109)))))))))))))))))))))))))))))))))))) (allB_succ 35
  109 (allA_of_3_1 35 35 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 109 (allA_succ_of_accept 33 34 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 109 (accept_3_3 32 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 34 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 109 (accept_3_3 29 34 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 109 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 34 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 109
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 109 (accept_3_3 26 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 109 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 34 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 109 (accept_3_3 23 34 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 34 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 109 (accept_3_3 20 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 109 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 34 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 109 (accept_3_3 17 34 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 34 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 109
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 109 (accept_3_3 14 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 109 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 34 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 109 (accept_3_3 11 34 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 34 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 109 (accept_3_3 8 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 109 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 34 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 109 (accept_3_3 5 34 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 34 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 109 (accept_3_3 2 34 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 109 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1
  34 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 109))))))))))))))))))))))))))))))))))
  (allB_succ 33 109 (allA_succ_of_accept 32 33 109 (accept_3_3 32 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 33 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 33 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 109 (accept_3_3 29 33 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  33 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 109
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 109 (accept_3_3 26 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 109 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 33 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 109 (accept_3_3 23 33 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 33 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 109
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 109 (accept_3_3 20 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 109 (Polychromatic418967fa.accept_16_3_1_13_1_4968 19 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 109 (Polychromatic418967fa.accept_21_18_12_4_1_4967 18 33 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 109 (accept_3_3 17 33 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 109
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 109 (accept_3_3 14 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 109 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 109 (accept_3_3 11 33 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 33 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 109
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 109 (accept_3_3 8 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  109 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 33 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 33 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 109 (accept_3_3 5 33 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 33
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 109 (accept_3_3 2 33 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 1
  33 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 109)))))))))))))))))))))))))))))))))
  (allB_succ 32 109 (allA_of_3_1 32 32 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 109
  (allA_succ_of_accept 30 31 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 109 (accept_3_3 29 31 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 109 (Polychromatic418967fa.accept_10_8_1_9_1_413 28 31 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 27
  31 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 109 (accept_3_3 26 31
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 109
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 31 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 109 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 109 (accept_3_3 23 31 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 109 (Polychromatic418967fa.accept_9_3_4_1_1_22 21
  31 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 109 (accept_3_3 20 31
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 109
  (Polychromatic418967fa.accept_11_8_9_10_1_503 19 31 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 109 (accept_3_3 17 31 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 31 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  31 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 109 (accept_3_3 14 31
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 109
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 31 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 109 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 31 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 109 (accept_3_3 11 31 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 109 (Polychromatic418967fa.accept_19_9_12_14_1_4966
  9 31 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 109 (accept_3_3 8 31
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 109 (Polychromatic418967fa.accept_9_7_4_1_1_391
  7 31 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 109 (accept_3_3 5 31 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  109 (Polychromatic418967fa.accept_17_4_14_7_1_4965 4 31 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 109 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 31 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 109 (accept_3_3 2 31 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 31 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 109))))))))))))))))))))))))))))))) (allB_succ 30 109
  (allA_succ_of_accept 29 30 109 (accept_3_3 29 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 109 (Polychromatic418967fa.accept_13_2_4_5_1_3152 28 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 109 (accept_3_3 26 30 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 30 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 109
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 109 (accept_3_3 23 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 109 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 109 (Polychromatic418967fa.accept_18_3_12_1_1_3787 21 30 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 109 (accept_3_3 20 30 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 109
  (Polychromatic418967fa.accept_21_18_9_4_1_4964 18 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 109 (accept_3_3 17 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 109 (accept_3_3 14 30 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 30 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 109
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 109 (accept_3_3 11 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  30 109 (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 30 109 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 30 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 109 (accept_3_3 8 30 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 109
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 109 (accept_3_3 5 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  109 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 30 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 30 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 109 (accept_3_3 2 30 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 30 109 (Polychromatic418967fa.accept_13_1_4_5_1_113 1 30 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 109)))))))))))))))))))))))))))))) (allB_succ 29 109 (allA_of_3_1
  29 29 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 109 (allA_succ_of_accept 27 28 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 109 (accept_3_3 26 28 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 28 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 109 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 28 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 109 (accept_3_3 23 28 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 109 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 28 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 109 (accept_3_3 20 28 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 109 (Polychromatic418967fa.accept_20_19_8_9_1_4963 19 28 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 109 (Polychromatic418967fa.accept_17_1_11_7_1_4962 18 28 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 109 (accept_3_3 17 28 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 109 (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 28
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 109 (accept_3_3 14 28 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 109 (Polychromatic418967fa.accept_17_13_11_7_1_4961 13 28 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 109 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 28 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 109 (accept_3_3 11 28 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 109 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 28
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 109 (accept_3_3 8 28 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  109 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 28 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 109 (Polychromatic418967fa.accept_15_6_13_4_1_2040 6 28 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 109 (accept_3_3 5 28 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 109 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 28 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 109 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 109 (accept_3_3 2 28 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 109 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 28
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 109))))))))))))))))))))))))))))
  (allB_succ 27 109 (allA_succ_of_accept 26 27 109 (accept_3_3 26 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 109 (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 27 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 109 (accept_3_3 23 27 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  27 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 109
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 109 (accept_3_3 20 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 109 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 109 (accept_3_3 17 27 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 109
  (Polychromatic418967fa.accept_11_4_5_10_1_926 15 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 109 (accept_3_3 14 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 109 (Polychromatic418967fa.accept_19_13_8_14_1_4960 13 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 109 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 109 (accept_3_3 11 27 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 109
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 109 (accept_3_3 8 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  109 (Polychromatic418967fa.accept_15_7_12_4_1_1236 7 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 109 (accept_3_3 5 27 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 109
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 109 (accept_3_3 2 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  109 (Polychromatic418967fa.accept_15_1_12_4_1_2022 1 27 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 109))))))))))))))))))))))))))) (allB_succ 26 109 (allA_of_3_1 26 26 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 25 109 (allA_succ_of_accept 24 25 109 (Polychromatic418967fa.accept_9_6_7_1_1_145 24
  25 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 109 (accept_3_3 23 25
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 109
  (Polychromatic418967fa.accept_9_4_7_1_1_379 22 25 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 25 109 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 25 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 109 (accept_3_3 20 25 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 25 109 (Polychromatic418967fa.accept_13_6_12_5_1_2304 19 25 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 109
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 25 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 109 (accept_3_3 17 25 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 109 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 25 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 109 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 25 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 109 (accept_3_3 14 25 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 25 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 109
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 25 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 109 (accept_3_3 11 25 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 109 (Polychromatic418967fa.accept_19_10_6_14_1_4959 10 25 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 109 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 25 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 109 (accept_3_3 8 25 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 109 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 25 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 109
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 25 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 109 (accept_3_3 5 25 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  109 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 25 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 109 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 25 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 109 (accept_3_3 2 25 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 109 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 25 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 109))))))))))))))))))))))))) (allB_succ 24 109
  (allA_succ_of_accept 23 24 109 (accept_3_3 23 24 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  24 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 24 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 24 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 109 (accept_3_3 20 24 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 109 (Polychromatic418967fa.accept_13_6_11_5_1_133 19 24 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 109
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 24 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 109 (accept_3_3 17 24 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 24 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 109 (accept_3_3 14 24 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 109
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 24 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 109 (accept_3_3 11 24 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 109 (Polychromatic418967fa.accept_15_10_9_4_1_2924 10 24 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 109 (Polychromatic418967fa.accept_18_9_6_1_1_3687 9 24 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 109 (accept_3_3 8 24 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 109
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 24 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 109 (accept_3_3 5 24 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  109 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 24 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 109 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 109 (accept_3_3 2 24 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 109)))))))))))))))))))))))) (allB_succ 23 109 (allA_of_3_1 23 23
  109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 109 (allA_succ_of_accept 21 22 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 109 (accept_3_3 20 22 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 109 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 22 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 109 (accept_3_3 17 22 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 22 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 109
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 109 (accept_3_3 14 22 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 109 (Polychromatic418967fa.accept_20_13_2_9_1_4958 13 22 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 109 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 22 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 109 (accept_3_3 11 22 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 22 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 109 (accept_3_3 8 22 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 109 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 22 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 109 (accept_3_3 5 22 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 109 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 22 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 109 (accept_3_3 2 22 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 109 (Polychromatic418967fa.accept_10_1_2_9_1_152 1
  22 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 109)))))))))))))))))))))) (allB_succ
  21 109 (allA_succ_of_accept 20 21 109 (accept_3_3 20 21 109 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 109 (Polychromatic418967fa.accept_23_19_21_17_1_4957 19 21 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 109 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 21 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 109 (accept_3_3 17 21 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  21 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 109
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 21 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 109 (accept_3_3 14 21 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 109 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 21 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 109 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 21 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 109 (accept_3_3 11 21 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 21 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 109
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 21 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 109 (accept_3_3 8 21 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  109 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 21 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 109 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 21 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 109 (accept_3_3 5 21 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 109 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  21 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 109 (accept_3_3 2 21 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 109 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1
  21 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 109))))))))))))))))))))) (allB_succ
  20 109 (allA_of_3_1 20 20 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 109 (allA_succ_of_accept 18 19
  109 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 109 (accept_3_3 17 19 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 19 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 19 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 109 (accept_3_3 14 19 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 109 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 19 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 109
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 19 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 109 (accept_3_3 11 19 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 19 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 109 (accept_3_3 8 19 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 109 (Polychromatic418967fa.accept_21_7_19_4_1_4956 7 19 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 109 (accept_3_3 5 19 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  109 (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 19 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 19 109 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 19 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 109 (accept_3_3 2 19 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 19 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 109))))))))))))))))))) (allB_succ 18 109
  (allA_succ_of_accept 17 18 109 (accept_3_3 17 18 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  18 109 (Polychromatic418967fa.accept_15_1_3_4_1_1217 16 18 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 18 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 109 (accept_3_3 14 18 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 109 (Polychromatic418967fa.accept_19_13_18_14_1_3522 13 18 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 109
  (Polychromatic418967fa.accept_21_12_18_4_1_4955 12 18 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 18 109 (accept_3_3 11 18 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  18 109 (Polychromatic418967fa.accept_17_10_1_7_1_4954 10 18 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 18 109 (Polychromatic418967fa.accept_21_9_18_4_1_4953 9 18 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 109 (accept_3_3 8 18 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 109
  (Polychromatic418967fa.accept_21_6_18_4_1_4952 6 18 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 109 (accept_3_3 5 18 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18
  109 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 18 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 18 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 109 (accept_3_3 2 18 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 18 109 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 18 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 109)))))))))))))))))) (allB_succ 17 109 (allA_of_3_1 17 17 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 109 (allA_succ_of_accept 15 16 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 109 (accept_3_3 14 16 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 16 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 109 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 16 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 109 (accept_3_3 11 16 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 109 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 16 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 109 (accept_3_3 8 16 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  109 (Polychromatic418967fa.accept_18_7_16_1_1_4951 7 16 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 16 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 16 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 109 (accept_3_3 5 16 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 16 109 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 16 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 16 109 (accept_3_3 2 16 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16
  109 (Polychromatic418967fa.accept_13_1_3_5_1_140 1 16 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 109)))))))))))))))) (allB_succ 15 109 (allA_succ_of_accept 14 15 109 (accept_3_3 14 15 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 109 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 15 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 109
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 15 109 (accept_3_3 11 15 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  15 109 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 15 109 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 15 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 109 (accept_3_3 8 15 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 109 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 15 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 109 (accept_3_3 5 15 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 109 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 109 (accept_3_3 2 15 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 109 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 15 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 109))))))))))))))) (allB_succ 14 109 (allA_of_3_1 14 14 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 109 (allA_succ_of_accept 12 13 109
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 109 (accept_3_3 11 13 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 13 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 109 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 13 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 109 (accept_3_3 8 13 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 109 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 13 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 109
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 13 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 109 (accept_3_3 5 13 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  109 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 13 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 109 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 13 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 109 (accept_3_3 2 13 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 109 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 13 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 109))))))))))))) (allB_succ 12 109
  (allA_succ_of_accept 11 12 109 (accept_3_3 11 12 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  12 109 (Polychromatic418967fa.accept_16_10_12_13_1_4950 10 12 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 109 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 109 (accept_3_3 8 12 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 109 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 109
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 12 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 109 (accept_3_3 5 12 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12
  109 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 12 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 12 109 (Polychromatic418967fa.accept_17_3_12_7_1_4949 3 12 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 109 (accept_3_3 2 12 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 12 109 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 109)))))))))))) (allB_succ 11 109 (allA_of_3_1 11 11 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 109 (allA_succ_of_accept 9 10 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 109 (accept_3_3 8 10 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  109 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 109 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 10 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 109 (accept_3_3 5 10 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 109 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 10 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 109 (accept_3_3 2 10 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  10 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 109)))))))))) (allB_succ 9 109
  (allA_succ_of_accept 8 9 109 (accept_3_3 8 9 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 109
  (Polychromatic418967fa.accept_16_7_9_13_1_4948 7 9 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 109 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 9 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 109 (accept_3_3 5 9 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 109 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 109 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 9
  109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 109 (accept_3_3 2 9 109
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 109 (Polychromatic418967fa.accept_11_1_9_10_1_184 1
  9 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 109))))))))) (allB_succ 8 109
  (allA_of_3_1 8 8 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 109 (allA_succ_of_accept 6 7 109
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 109 (accept_3_3 5 7 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 109
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 109 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 7 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 109 (accept_3_3 2 7 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 109 (Polychromatic418967fa.accept_21_1_7_4_1_4947 1 7 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 109))))))) (allB_succ 6 109 (allA_succ_of_accept 5 6 109
  (accept_3_3 5 6 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 109
  (Polychromatic418967fa.accept_9_4_6_1_1_393 4 6 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 109 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 109 (accept_3_3 2 6 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 109 (Polychromatic418967fa.accept_13_1_6_5_1_1610 1 6 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 109)))))) (allB_succ 5 109 (allA_of_3_1 5 5 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 109 (allA_succ_of_accept 3 4 109
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 109 (accept_3_3 2 4 109 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 109
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 4 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 109)))) (allB_succ 3 109 (allA_succ_of_accept 2 3 109 (accept_3_3 2 3 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 109 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 3 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 109))) (allB_succ 2 109 (allA_of_3_1 2 2 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  109)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


