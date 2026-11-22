-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch113
-- name    : Polychromatic418967fa_Branch113
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:11:00.13257+00:00
-- url     : https://prove2.me/theorems/0eac7144-0634-46d9-8874-7567ec710a52
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

def Polychromatic418967fa.branch_113 : allB 113 113 :=
  allB_succ' 2 112 113 (Eq.refl Bool.true) (allA_of_3_0 2 112 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  111 113 (Eq.refl Bool.true) (allA_succ_of_accept 2 111 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 113 (accept_3_2 1 111 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111 113))) (allB_succ' 4 110 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 110 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 113 (Polychromatic418967fa.accept_13_2_6_9_1_2636 2 110 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 113 (accept_3_2 1 110 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110 113)))) (allB_succ' 5 109 113 (Eq.refl Bool.true) (allA_of_3_0
  5 109 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 108 113 (Eq.refl Bool.true) (allA_succ_of_accept 5
  108 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 108 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 108 113 (accept_3_2 4 108 113 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 108 113 (Polychromatic418967fa.accept_20_3_8_13_1_3832 3 108 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 108 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 113 (accept_3_2 1 108 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108 113)))))) (allB_succ' 7 107 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 107 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 113 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 107 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 113 (accept_3_2 4 107 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  107 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 113 (accept_3_2 1 107 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107 113)))))))
  (allB_succ' 8 106 113 (Eq.refl Bool.true) (allA_of_3_0 8 106 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 105 113 (Eq.refl Bool.true) (allA_succ_of_accept 8 105 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 113 (accept_3_2 7 105 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 113 (Polychromatic418967fa.accept_13_6_1_9_1_619 6
  105 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 113
  (Polychromatic418967fa.accept_13_5_1_9_1_618 5 105 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 113 (accept_3_2 4 105 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 105 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 113 (accept_3_2 1 105 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105 113))))))))) (allB_succ' 10 104 113 (Eq.refl Bool.true) (allA_succ_of_accept 9 104
  113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 104 113 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 104 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 113 (accept_3_2 7 104 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 104 113 (Polychromatic418967fa.accept_15_6_14_8_1_245 6 104 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 5
  104 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 113 (accept_3_2 4 104
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 113 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 104 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 113
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 104 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 113 (accept_3_2 1 104 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  113)))))))))) (allB_succ' 11 103 113 (Eq.refl Bool.true) (allA_of_3_0 11 103 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 102 113 (Eq.refl Bool.true) (allA_succ_of_accept 11 102 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 113 (accept_3_2 10 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 113 (Polychromatic418967fa.accept_18_9_12_5_1_864 9 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 113 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 102 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 113 (accept_3_2 7 102 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 102 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 113
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 113 (accept_3_2 4 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 102 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 113 (accept_3_2 1 102 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 102 113)))))))))))) (allB_succ' 13 101 113 (Eq.refl Bool.true) (allA_succ_of_accept 12
  101 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 101 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 101 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 113 (accept_3_2 10 101 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 101 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 113
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 101 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 113 (accept_3_2 7 101 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 101 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 101 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 113 (accept_3_2 4 101 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 101 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 113
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 101 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 113 (accept_3_2 1 101 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  113))))))))))))) (allB_succ' 14 100 113 (Eq.refl Bool.true) (allA_of_3_0 14 100 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 99 113 (Eq.refl Bool.true) (allA_succ_of_accept 14 99 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 113 (accept_3_2 13 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 113 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 113 (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 99 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 113 (accept_3_2 10 99 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 113 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 99 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 113 (accept_3_2 7 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 113 (Polychromatic418967fa.accept_19_5_4_18_1_5242 5 99 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 113 (accept_3_2 4 99 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 113 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3 99 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 113 (accept_3_2 1 99 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 113))))))))))))))) (allB_succ' 16 98 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 98 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 113 (Polychromatic418967fa.accept_18_14_8_5_1_860 14 98 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 98 113 (accept_3_2 13 98 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 98 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 12
  98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 98 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 98 113 (accept_3_2 10 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  98 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 98 113 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 98 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 98 113 (accept_3_2 7 98 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 98 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 98 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 98 113
  (Polychromatic418967fa.accept_10_5_8_3_1_229 5 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 98 113 (accept_3_2 4 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 98
  113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 98 113 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 98 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 113 (accept_3_2 1 98 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 113)))))))))))))))) (allB_succ' 17 97 113 (Eq.refl Bool.true) (allA_of_3_0 17 97 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 96 113 (Eq.refl Bool.true) (allA_succ_of_accept 17 96 113
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 113 (accept_3_2 16 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 113 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 113 (Polychromatic418967fa.accept_13_1_5_9_1_226 14 96 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 113 (accept_3_2 13 96 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 96 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 113
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 113 (accept_3_2 10 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 113 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 113 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 96 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 113 (accept_3_2 7 96 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 96 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 113
  (Polychromatic418967fa.accept_11_5_8_3_1_66 5 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 113 (accept_3_2 4 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  113 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 96 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 113 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 96 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 113 (accept_3_2 1 96 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96 113)))))))))))))))))) (allB_succ' 19 95 113 (Eq.refl Bool.true) (allA_succ_of_accept 18 95
  113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 95 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 113 (accept_3_2 16 95 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 95 113 (Polychromatic418967fa.accept_11_4_7_3_1_289 15 95 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 113 (accept_3_2 13 95
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 113
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 95 113 (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 95 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 113 (accept_3_2 10 95 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 95 113 (Polychromatic418967fa.accept_27_9_14_5_1_5287 9 95 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 113 (Polychromatic418967fa.accept_10_8_5_3_1_543 8
  95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 113 (accept_3_2 7 95 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 113
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 113 (accept_3_2 4 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  113 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 95 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 113 (accept_3_2 1 95 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 113))))))))))))))))))) (allB_succ' 20 94 113 (Eq.refl Bool.true) (allA_of_3_0 20 94 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 93 113 (Eq.refl Bool.true) (allA_succ_of_accept 20 93 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 113 (accept_3_2 19 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 113 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 93 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 113 (accept_3_2 16 93 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 93 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 113 (accept_3_2 13 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 113 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 93 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 113 (accept_3_2 10 93 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 113 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 93 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 113 (accept_3_2 7 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  113 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 93 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 113 (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 93 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 113 (accept_3_2 4 93 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 93 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 113 (accept_3_2 1 93 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 113))))))))))))))))))))) (allB_succ' 22 92 113 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 92 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 113 (Polychromatic418967fa.accept_16_4_12_1_1_1204
  20 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 92 113 (accept_3_2 19
  92 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 92 113
  (Polychromatic418967fa.accept_11_7_4_3_1_302 18 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 92 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 92 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 113 (accept_3_2 16 92 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 92 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 113 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 92 113 (accept_3_2 13
  92 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 92 113
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 92 113 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 92 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 113 (accept_3_2 10 92 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 92 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 8
  92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 92 113 (accept_3_2 7 92 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 92 113
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 92 113 (accept_3_2 4 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 92
  113 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 92 113 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 92 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 113 (accept_3_2 1 92 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 113)))))))))))))))))))))) (allB_succ' 23 91 113 (Eq.refl Bool.true) (allA_of_3_0 23 91 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 90 113 (Eq.refl Bool.true) (allA_succ_of_accept 23 90 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 113 (accept_3_2 22 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 113 (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 90 113 (Polychromatic418967fa.accept_19_1_14_18_1_3919 20 90 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 113 (accept_3_2 19 90 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 113 (Polychromatic418967fa.accept_26_18_12_9_1_5286 18 90
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 113
  (Polychromatic418967fa.accept_20_17_10_13_1_1400 17 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 90 113 (accept_3_2 16 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 90 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 113 (Polychromatic418967fa.accept_21_14_6_8_1_1285 14 90
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 113 (accept_3_2 13 90 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 12
  90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 113 (accept_3_2 10 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 90 113 (Polychromatic418967fa.accept_13_8_12_9_1_1168 8 90 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 113 (accept_3_2 7 90 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 113 (Polychromatic418967fa.accept_17_6_5_11_1_4073 6 90 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 113
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 113 (accept_3_2 4 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90
  113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 90 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 113 (accept_3_2 1 90 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 90 113)))))))))))))))))))))))) (allB_succ' 25 89 113 (Eq.refl Bool.true) (allA_succ_of_accept 24
  89 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 113 (Polychromatic418967fa.accept_17_6_4_11_1_4072 23 89 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 113 (accept_3_2 22 89 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 89 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 113
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 113 (accept_3_2 19 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 113 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 89 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 113 (accept_3_2 16 89 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 89 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 113
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 113 (accept_3_2 13 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 113 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 89 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 113 (accept_3_2 10 89 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 113 (Polychromatic418967fa.accept_15_9_14_8_1_1396 9 89 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 113
  (Polychromatic418967fa.accept_13_8_11_9_1_593 8 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 113 (accept_3_2 7 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  113 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 113 (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 89 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 113 (accept_3_2 4 89 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 89 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 113 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  89 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 113 (accept_3_2 1 89 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 113))))))))))))))))))))))))) (allB_succ' 26 88 113 (Eq.refl
  Bool.true) (allA_of_3_0 26 88 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 87 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 87 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 113 (accept_3_2 25 87 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 113 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 87 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 23
  87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 113 (accept_3_2 22 87
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 113 (Polychromatic418967fa.accept_9_3_6_5_1_63
  21 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 113 (accept_3_2 19 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 113 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 87 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 113 (accept_3_2 16 87 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 113 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 87 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 113 (accept_3_2 13 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 87 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 113 (accept_3_2 10 87 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 87 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 113 (accept_3_2 7 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 87 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 113 (accept_3_2 4 87 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 113 (accept_3_2 1 87 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 113))))))))))))))))))))))))))) (allB_succ' 28 86 113 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 86 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 113 (Polychromatic418967fa.accept_18_8_14_5_1_2778
  26 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 86 113 (accept_3_2 25
  86 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 86 113
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 86 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 113 (accept_3_2 22 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 86 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 20
  86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 86 113 (accept_3_2 19 86
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 86 113
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 86 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 113 (accept_3_2 16 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 86 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 113 (Polychromatic418967fa.accept_13_1_8_9_1_1154
  14 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 86 113 (accept_3_2 13
  86 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 86 113
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 86 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 113 (accept_3_2 10 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 86 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 113 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8
  86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 86 113 (accept_3_2 7 86 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 6
  86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 86 113
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 86 113 (accept_3_2 4 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 86
  113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 86 113 (Polychromatic418967fa.accept_16_2_6_1_1_2069 2 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 113 (accept_3_2 1 86 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 113)))))))))))))))))))))))))))) (allB_succ' 29 85 113 (Eq.refl Bool.true) (allA_of_3_0 29 85
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 84 113 (Eq.refl Bool.true) (allA_succ_of_accept 29 84 113
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 113 (accept_3_2 28 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 113 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 113 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 113 (accept_3_2 25 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 84 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 113
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 113 (accept_3_2 22 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 113 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 113 (accept_3_2 19 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 113 (Polychromatic418967fa.accept_15_3_9_8_1_3164 18 84 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 113
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 113 (accept_3_2 16 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 113 (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 113 (accept_3_2 13 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 113 (Polychromatic418967fa.accept_16_12_4_1_1_1257 12 84 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 113
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 113 (accept_3_2 10 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 113 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 113 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 113 (accept_3_2 7 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 84 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 113
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 113 (accept_3_2 4 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  113 (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 84 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 84 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 113 (accept_3_2 1 84 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84 113)))))))))))))))))))))))))))))) (allB_succ' 31 83 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 30 83 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 113 (Polychromatic418967fa.accept_13_3_5_9_1_5285 29 83 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 113 (accept_3_2 28 83 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 113 (Polychromatic418967fa.accept_13_1_5_9_1_226
  27 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 113 (accept_3_2 25 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 83 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 113 (accept_3_2 22 83 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 83 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 113
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 113 (accept_3_2 19 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 83 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 113 (accept_3_2 16 83 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 83 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 113 (accept_3_2 13 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 113 (Polychromatic418967fa.accept_19_11_7_18_1_5284 11 83 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 113 (accept_3_2 10 83 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 83 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 113
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 113 (accept_3_2 7 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 83 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 113 (accept_3_2 4 83 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 83 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 83 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 113 (accept_3_2 1 83 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83 113))))))))))))))))))))))))))))))) (allB_succ' 32 82 113
  (Eq.refl Bool.true) (allA_of_3_0 32 82 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 81 113 (Eq.refl
  Bool.true) (allA_succ_of_accept 32 81 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 113 (accept_3_2 31 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 113 (Polychromatic418967fa.accept_18_12_9_5_1_2771 30 81 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 113
  (Polychromatic418967fa.accept_11_7_4_3_1_302 29 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 113 (accept_3_2 28 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 113 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 113 (accept_3_2 25 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 81 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 113
  (Polychromatic418967fa.accept_17_6_13_11_1_995 23 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 113 (accept_3_2 22 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 113 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 113 (accept_3_2 19 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 113 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 81 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 113
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 113 (accept_3_2 16 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 113 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 113 (accept_3_2 13 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 81 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 113
  (Polychromatic418967fa.accept_21_11_18_8_1_5264 11 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 113 (accept_3_2 10 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 113 (Polychromatic418967fa.accept_19_9_5_18_1_3891 9 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 113 (accept_3_2 7 81 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 113 (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 81 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 113
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 113 (accept_3_2 4 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  113 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 81 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 113 (accept_3_2 1 81 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 113))))))))))))))))))))))))))))))))) (allB_succ' 34 80 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 80 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 80 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 80 113 (accept_3_2 31 80 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 80 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 30
  80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 80 113
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 80 113 (accept_3_2 28 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  80 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 80 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 80 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 80 113 (accept_3_2 25 80 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 80 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 80 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 113
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 80 113 (accept_3_2 22 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  80 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 80 113 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 80 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 80 113 (accept_3_2 19 80 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 80 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 80 113
  (Polychromatic418967fa.accept_18_17_8_5_1_2769 17 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 80 113 (accept_3_2 16 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  80 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 80 113 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 80 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 113 (accept_3_2 13 80 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 80 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 80 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 113
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 80 113 (accept_3_2 10 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  80 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 80 113 (Polychromatic418967fa.accept_19_8_4_18_1_5283 8 80 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 113 (accept_3_2 7 80 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 80 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 80 113
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 80 113 (accept_3_2 4 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80
  113 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 80 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 80 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 113 (accept_3_2 1 80 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 113)))))))))))))))))))))))))))))))))) (allB_succ' 35 79 113 (Eq.refl Bool.true) (allA_of_3_0
  35 79 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 78 113 (Eq.refl Bool.true) (allA_succ_of_accept 35
  78 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 78 113 (accept_3_2 34 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 78 113 (Polychromatic418967fa.accept_18_15_6_5_1_3972 33 78 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 113 (Polychromatic418967fa.accept_24_8_6_17_1_5282 32 78
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 113 (accept_3_2 31 78 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 30
  78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 113
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 113 (accept_3_2 28 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 113 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 78 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 113 (accept_3_2 25 78 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 113 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 78 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 113 (accept_3_2 22 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 113 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 78 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 113 (accept_3_2 19 78 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 113 (Polychromatic418967fa.accept_17_1_10_11_1_2943 18 78 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 113
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 113 (accept_3_2 16 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 113 (Polychromatic418967fa.accept_21_14_15_8_1_5281 14 78 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 113 (accept_3_2 13 78 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 78 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 113 (accept_3_2 10 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 113 (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 78 113 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 78 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 113 (accept_3_2 7 78 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 113 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 78 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 113
  (Polychromatic418967fa.accept_10_5_8_3_1_229 5 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 113 (accept_3_2 4 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78
  113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 113 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 78 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 113 (accept_3_2 1 78 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 113)))))))))))))))))))))))))))))))))))) (allB_succ' 37 77 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 77 113 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 77 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 113 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 77 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 77 113 (accept_3_2 34 77 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 113
  (Polychromatic418967fa.accept_19_14_1_18_1_5280 33 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 77 113 (Polychromatic418967fa.accept_19_13_1_18_1_5279 32 77 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 113 (accept_3_2 31 77 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 77 113 (Polychromatic418967fa.accept_16_14_13_1_1_5278 30 77 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 113
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 113 (accept_3_2 28 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 113 (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 113 (Polychromatic418967fa.accept_10_6_7_3_1_547 26 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 113 (accept_3_2 25 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 113 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 77 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 113
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 113 (accept_3_2 22 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 113 (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 113 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 113 (accept_3_2 19 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 113 (Polychromatic418967fa.accept_27_18_23_5_1_5277 18 77 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 113
  (Polychromatic418967fa.accept_19_17_1_18_1_2693 17 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 113 (accept_3_2 16 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 113 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 113 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 113 (accept_3_2 13 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 113 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 77 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 113
  (Polychromatic418967fa.accept_19_11_1_18_1_5276 11 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 113 (accept_3_2 10 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 113 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 113 (Polychromatic418967fa.accept_13_8_12_9_1_1168 8 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 113 (accept_3_2 7 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 113 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 77 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 113
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 113 (accept_3_2 4 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  113 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 77 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 77 113 (Polychromatic418967fa.accept_17_2_9_11_1_4057 2 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 113 (accept_3_2 1 77 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 77 113))))))))))))))))))))))))))))))))))))) (allB_succ' 38 76 113 (Eq.refl Bool.true)
  (allA_of_3_0 38 76 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 75 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 113 (accept_3_2 37 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 113 (Polychromatic418967fa.accept_21_15_12_8_1_5275 36 75 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 113
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 113 (accept_3_2 34 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  75 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 75 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 113 (accept_3_2 31 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 113
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 113 (accept_3_2 28 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  75 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 75 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 113 (accept_3_2 25 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 75 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 113
  (Polychromatic418967fa.accept_22_1_9_3_1_3674 23 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 113 (accept_3_2 22 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  75 113 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 75 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 113 (accept_3_2 19 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 113
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 113 (accept_3_2 16 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  75 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 75 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 113 (accept_3_2 13 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 113 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 75 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 113
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 113 (accept_3_2 10 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  75 113 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 113 (accept_3_2 7 75 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 113
  (Polychromatic418967fa.accept_17_5_7_11_1_5274 5 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 113 (accept_3_2 4 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75
  113 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 113 (accept_3_2 1 75 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 75 113))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 74 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 74 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 74 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 74 113 (accept_3_2 37 74 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 74 113 (Polychromatic418967fa.accept_15_6_14_8_1_245
  36 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 74 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 74 113 (accept_3_2 34 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  74 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 74 113 (Polychromatic418967fa.accept_12_8_2_5_1_844 32 74 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 113 (accept_3_2 31 74 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 74 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 74 113
  (Polychromatic418967fa.accept_10_9_4_3_1_539 29 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 74 113 (accept_3_2 28 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  74 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 74 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 74 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 113 (accept_3_2 25 74 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 74 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 74 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 74 113 (accept_3_2 22 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  74 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 74 113 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 74 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 113 (accept_3_2 19 74 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 113 (Polychromatic418967fa.accept_21_18_11_8_1_5273 18 74 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 74 113
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 74 113 (accept_3_2 16 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  74 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 74 113 (Polychromatic418967fa.accept_21_14_11_8_1_5272 14 74 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 113 (accept_3_2 13 74 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 74 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 74 113 (accept_3_2 10 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  74 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 74 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 74 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 113 (accept_3_2 7 74 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 74 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 113
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 113 (accept_3_2 4 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 113 (Polychromatic418967fa.accept_25_2_24_13_1_5271 2 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 113 (accept_3_2 1 74 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 113)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 73 113 (Eq.refl Bool.true)
  (allA_of_3_0 41 73 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 72 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 113 (accept_3_2 40 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 113 (Polychromatic418967fa.accept_16_7_8_1_1_3061 39 72 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 38
  72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 113 (accept_3_2 37 72
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 113
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 113 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 113 (accept_3_2 34 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 113 (Polychromatic418967fa.accept_15_3_12_8_1_738 33 72 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 113 (Polychromatic418967fa.accept_13_6_7_9_1_1848
  32 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 113 (accept_3_2 31
  72 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 113
  (Polychromatic418967fa.accept_11_8_6_3_1_661 30 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 113 (Polychromatic418967fa.accept_13_3_7_9_1_1153 29 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 113 (accept_3_2 28 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 72 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 113 (Polychromatic418967fa.accept_15_11_12_8_1_739
  26 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 113 (accept_3_2 25
  72 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 113
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 113 (Polychromatic418967fa.accept_16_7_8_1_1_3061 23 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 113 (accept_3_2 22 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 113 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 72 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 20
  72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 113 (accept_3_2 19 72
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 113
  (Polychromatic418967fa.accept_15_3_12_8_1_738 18 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 113 (accept_3_2 16 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 113 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 72 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 113
  (Polychromatic418967fa.accept_19_14_15_18_1_5250 14 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 72 113 (accept_3_2 13 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 72 113 (Polychromatic418967fa.accept_16_12_8_1_1_5270 12 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 113 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 72 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 113 (accept_3_2 10 72 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 72 113 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9
  72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 113
  (Polychromatic418967fa.accept_11_8_6_3_1_661 8 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 72 113 (accept_3_2 7 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72
  113 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 113 (Polychromatic418967fa.accept_10_5_2_3_1_239 5 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 113 (accept_3_2 4 72 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 72 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 113 (Polychromatic418967fa.accept_13_2_7_9_1_2616 2
  72 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 113 (accept_3_2 1 72 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 113)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 71
  113 (Eq.refl Bool.true) (allA_succ_of_accept 42 71 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 113
  (Polychromatic418967fa.accept_11_8_5_3_1_694 41 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 113 (accept_3_2 40 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 113 (accept_3_2 37 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 113 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 71 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 113
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 113 (accept_3_2 34 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 113 (Polychromatic418967fa.accept_10_2_1_3_1_233 32 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 113 (accept_3_2 31 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 113
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 113 (accept_3_2 28 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 113 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 113 (accept_3_2 25 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 71 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 113
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 113 (accept_3_2 22 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 113 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 113 (accept_3_2 19 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 113
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 17 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 113 (accept_3_2 16 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 113 (accept_3_2 13 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 71 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 113
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 113 (accept_3_2 10 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 113 (Polychromatic418967fa.accept_17_9_3_11_1_3983 9 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 113 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 113 (accept_3_2 7 71 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 113
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 113 (accept_3_2 4 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  113 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 71 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 113 (accept_3_2 1 71 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 113))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 70 113 (Eq.refl Bool.true)
  (allA_of_3_0 44 70 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 69 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 69 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 113 (accept_3_2 43 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 113 (Polychromatic418967fa.accept_17_8_1_11_1_4004 42 69 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 113
  (Polychromatic418967fa.accept_16_9_5_1_1_1259 41 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 113 (accept_3_2 40 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  69 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 69 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 113 (accept_3_2 37 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 113 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 69 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 113
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 113 (accept_3_2 34 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  69 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 69 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 113 (accept_3_2 31 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 69 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 113
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 113 (accept_3_2 28 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 113 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 113 (accept_3_2 25 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 113 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 69 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 113
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 113 (accept_3_2 22 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  69 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 69 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 113 (accept_3_2 19 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 113 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 69 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 113
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 113 (accept_3_2 16 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 113 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 113 (accept_3_2 13 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 113
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 113 (accept_3_2 10 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 113 (accept_3_2 7 69 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 113 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 69 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 113
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 113 (accept_3_2 4 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  113 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 69 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 113 (accept_3_2 1 69 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 113))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 68 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 68 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 113 (Polychromatic418967fa.accept_13_5_3_9_1_1189 44 68 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 113 (accept_3_2 43 68 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 113
  (Polychromatic418967fa.accept_19_4_11_18_1_3909 42 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 113 (accept_3_2 40 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 113 (accept_3_2 37 68
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 113
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 113 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 113 (accept_3_2 34 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 113 (Polychromatic418967fa.accept_7_4_5_1_1_418 32
  68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 113 (accept_3_2 31 68
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 113
  (Polychromatic418967fa.accept_16_14_4_1_1_3049 30 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 68 113 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 113 (accept_3_2 28 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 68 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 113 (Polychromatic418967fa.accept_10_6_8_3_1_930
  26 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 113 (accept_3_2 25
  68 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 113
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 68 113 (Polychromatic418967fa.accept_11_1_2_3_1_688 23 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 113 (accept_3_2 22 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 68 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 20
  68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 113 (accept_3_2 19 68
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 113
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 68 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 113 (accept_3_2 16 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 68 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 113 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 113 (accept_3_2 13
  68 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 113
  (Polychromatic418967fa.accept_11_1_2_3_1_688 12 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 68 113 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 113 (accept_3_2 10 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 68 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 113 (Polychromatic418967fa.accept_13_8_3_9_1_5269 8
  68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 113 (accept_3_2 7 68 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 6
  68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 113
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 113 (accept_3_2 4 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  113 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 113 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 113 (accept_3_2 1 68 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 113)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 67 113 (Eq.refl Bool.true)
  (allA_of_3_0 47 67 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 66 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 66 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 113 (accept_3_2 46 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 66 113 (Polychromatic418967fa.accept_13_6_1_9_1_619 45 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 44
  66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 113 (accept_3_2 43 66
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 113
  (Polychromatic418967fa.accept_9_6_3_5_1_240 42 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 66 113 (Polychromatic418967fa.accept_13_2_1_9_1_1174 41 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 113 (accept_3_2 40 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 66 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 38
  66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 113 (accept_3_2 37 66
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 113
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 113 (accept_3_2 34 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 66 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 113 (accept_3_2 31 66
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 113 (Polychromatic418967fa.accept_7_2_3_1_1_10
  30 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 113
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 113 (accept_3_2 28 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 113 (accept_3_2 25 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 66 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 113 (accept_3_2 22 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 113 (Polychromatic418967fa.accept_13_8_1_9_1_1178 21 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 113 (accept_3_2 19 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 66 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 113
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 113 (accept_3_2 16 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 113 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 66 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 113 (accept_3_2 13 66 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 66 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 113 (accept_3_2 10 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 113 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 113 (accept_3_2 7 66 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 66 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 113
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 113 (accept_3_2 4 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 113 (accept_3_2 1 66 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 113)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 65 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 65 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 113 (Polychromatic418967fa.accept_10_7_5_3_1_542 47 65 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 113 (accept_3_2 46 65 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 45
  65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 113
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 113 (accept_3_2 43 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 113 (accept_3_2 40 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 65 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 113
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 113 (accept_3_2 37 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 113 (Polychromatic418967fa.accept_14_8_9_1_1_3313 36 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 113 (accept_3_2 34 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 65 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 113
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 113 (accept_3_2 31 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 113 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 113 (accept_3_2 28 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 65 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 113
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 113 (accept_3_2 25 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 113 (Polychromatic418967fa.accept_19_4_8_18_1_5268 23 65 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 113 (accept_3_2 22 65 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 65 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 113
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 113 (accept_3_2 19 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 113 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 113 (accept_3_2 16 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 65 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 113
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 113 (accept_3_2 13 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 113 (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 65 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 113 (accept_3_2 10 65 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 113 (Polychromatic418967fa.accept_19_9_8_18_1_1571 9 65 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 113
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 113 (accept_3_2 7 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  113 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 113 (Polychromatic418967fa.accept_21_5_2_8_1_5267 5 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 113 (accept_3_2 4 65 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 65 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 113 (Polychromatic418967fa.accept_10_2_5_3_1_1408 2
  65 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 113 (accept_3_2 1 65 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65 113))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  50 64 113 (Eq.refl Bool.true) (allA_of_3_0 50 64 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 63 113
  (Eq.refl Bool.true) (allA_succ_of_accept 50 63 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 113 (accept_3_2 49 63 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 63 113 (Polychromatic418967fa.accept_14_6_7_1_1_78 48 63 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 113
  (Polychromatic418967fa.accept_13_8_11_9_1_593 47 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 113 (accept_3_2 46 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  63 113 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 63 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 113 (accept_3_2 43 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 63 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 113
  (Polychromatic418967fa.accept_13_2_11_9_1_591 41 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 113 (accept_3_2 40 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  63 113 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 63 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 113 (accept_3_2 37 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 113 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 63 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 113
  (Polychromatic418967fa.accept_15_5_3_8_1_748 35 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 113 (accept_3_2 34 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  63 113 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 63 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 113 (accept_3_2 31 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 113
  (Polychromatic418967fa.accept_22_7_19_3_1_5266 29 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 63 113 (accept_3_2 28 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  63 113 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 63 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 113 (accept_3_2 25 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 113 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 63 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 113
  (Polychromatic418967fa.accept_17_6_12_11_1_5231 23 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 113 (accept_3_2 22 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  63 113 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 63 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 113 (accept_3_2 19 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 113
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 113 (accept_3_2 16 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  63 113 (Polychromatic418967fa.accept_13_2_11_9_1_591 15 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 63 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 113 (accept_3_2 13 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 113 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 63 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 113
  (Polychromatic418967fa.accept_15_11_3_8_1_750 11 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 113 (accept_3_2 10 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  63 113 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 63 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 113 (accept_3_2 7 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 113
  (Polychromatic418967fa.accept_11_5_8_3_1_66 5 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 113 (accept_3_2 4 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63
  113 (Polychromatic418967fa.accept_19_3_6_18_1_2665 3 63 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 63 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 113 (accept_3_2 1 63 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 63 113))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 62 113
  (Eq.refl Bool.true) (allA_succ_of_accept 51 62 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 113
  (Polychromatic418967fa.accept_18_14_8_5_1_860 50 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 113 (accept_3_2 49 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 113 (accept_3_2 46 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 113
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 113 (accept_3_2 43 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 113 (Polychromatic418967fa.accept_10_1_2_3_1_1910 41 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 113 (accept_3_2 40 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 113
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 113 (accept_3_2 37 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 113 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 113 (accept_3_2 34 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 113
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 32 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 113 (accept_3_2 31 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 113 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 113 (accept_3_2 28 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 113
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 113 (accept_3_2 25 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 113 (accept_3_2 22 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 113
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 113 (accept_3_2 19 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 113 (Polychromatic418967fa.accept_20_18_2_13_1_5265 18 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 113 (Polychromatic418967fa.accept_18_17_8_5_1_2769 17 62 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 113 (accept_3_2 16 62 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 113
  (Polychromatic418967fa.accept_13_1_10_9_1_215 14 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 113 (accept_3_2 13 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 113 (accept_3_2 10 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 113
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 113 (accept_3_2 7 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  113 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 62 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 113 (accept_3_2 4 62 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 62
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 113 (accept_3_2 1 62 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62 113))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 61 113 (Eq.refl Bool.true) (allA_of_3_0 53 61 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  54 60 113 (Eq.refl Bool.true) (allA_succ_of_accept 53 60 113 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 60 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 113 (accept_3_2 52 60 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 60 113 (Polychromatic418967fa.accept_13_12_8_9_1_1833
  51 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 113
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 50 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 60 113 (accept_3_2 49 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  60 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 60 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 113 (accept_3_2 46 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 60 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 60 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 113
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 113 (accept_3_2 43 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  60 113 (Polychromatic418967fa.accept_13_3_8_9_1_1134 42 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 60 113 (Polychromatic418967fa.accept_11_8_5_3_1_694 41 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 113 (accept_3_2 40 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 60 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 113
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 60 113 (accept_3_2 37 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  60 113 (Polychromatic418967fa.accept_16_4_12_1_1_1204 36 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 60 113 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 113 (accept_3_2 34 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 60 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 113
  (Polychromatic418967fa.accept_21_11_18_8_1_5264 32 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 60 113 (accept_3_2 31 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  60 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 60 113 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 113 (accept_3_2 28 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 113 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 60 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 113
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 60 113 (accept_3_2 25 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  60 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 60 113 (Polychromatic418967fa.accept_19_4_3_18_1_2699 23 60 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 113 (accept_3_2 22 60 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 113 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 60 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 113
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 60 113 (accept_3_2 19 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  60 113 (Polychromatic418967fa.accept_16_2_12_1_1_3086 18 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 60 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 113 (accept_3_2 16 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 60 113 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 60 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 113
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 60 113 (accept_3_2 13 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  60 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 60 113 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 113 (accept_3_2 10 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 60 113 (Polychromatic418967fa.accept_19_9_3_18_1_5263 9 60 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 113
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 113 (accept_3_2 7 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60
  113 (Polychromatic418967fa.accept_19_6_3_18_1_5262 6 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 60 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 113 (accept_3_2 4 60 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 113
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 113 (accept_3_2 1 60 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  113)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 59 113 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 59 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 59 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 113 (accept_3_2 52 59 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 51
  59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 113 (accept_3_2 49 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 113 (Polychromatic418967fa.accept_17_14_8_11_1_4052 48 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 113 (accept_3_2 46 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 113 (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 59 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 113
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 113 (accept_3_2 43 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 113 (Polychromatic418967fa.accept_13_2_7_9_1_2616 41 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 113 (accept_3_2 40 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 59 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 113 (accept_3_2 37 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 113 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 113 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 59 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 113 (accept_3_2 34 59 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 59 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 113
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 113 (accept_3_2 31 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 113 (Polychromatic418967fa.accept_11_7_4_3_1_302 29 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 113 (accept_3_2 28 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 113 (Polychromatic418967fa.accept_22_5_15_3_1_5261 27 59 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 113 (accept_3_2 25 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 113 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 113 (accept_3_2 22 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 113 (Polychromatic418967fa.accept_13_8_7_9_1_611 21 59 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 113
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 113 (accept_3_2 19 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 113 (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 113 (accept_3_2 16 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 113 (Polychromatic418967fa.accept_13_2_7_9_1_2616 15 59 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 113 (accept_3_2 13 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 113 (accept_3_2 10 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 59 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 113
  (Polychromatic418967fa.accept_13_8_7_9_1_611 8 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 113 (accept_3_2 7 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 59 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 113 (accept_3_2 4 59 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 113 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 59 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 113 (accept_3_2 1 59 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 113)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 58 113 (Eq.refl Bool.true) (allA_of_3_0 56 58 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  57 113 (allA_succ_of_accept 56 57 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 113 (accept_3_2 55 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 57 113 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 57 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 113
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 57 113 (accept_3_2 52 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  57 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 57 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 113 (accept_3_2 49 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 113 (Polychromatic418967fa.accept_15_3_12_8_1_738 48 57 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 113
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 113 (accept_3_2 46 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  57 113 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 57 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 113 (accept_3_2 43 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 113
  (Polychromatic418967fa.accept_13_2_5_9_1_610 41 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 57 113 (accept_3_2 40 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  57 113 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 57 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 113 (accept_3_2 37 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 113 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 57 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 113
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 113 (accept_3_2 34 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  57 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 57 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 113 (accept_3_2 31 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 113 (Polychromatic418967fa.accept_13_4_5_9_1_1829 30 57 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 113
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 113 (accept_3_2 28 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  57 113 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 57 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 113 (accept_3_2 25 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 57 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 113
  (Polychromatic418967fa.accept_11_1_2_3_1_688 23 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 113 (accept_3_2 22 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  57 113 (Polychromatic418967fa.accept_16_5_9_1_1_2070 21 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 57 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 113 (accept_3_2 19 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 113 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 57 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 113
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 113 (accept_3_2 16 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  57 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 57 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 113 (accept_3_2 13 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 113 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 57 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 113
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 113 (accept_3_2 10 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  57 113 (Polychromatic418967fa.accept_23_9_11_21_1_5259 9 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 57 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 113 (accept_3_2 7 57 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 57 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 113
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 113 (accept_3_2 4 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57
  113 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 57 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 113 (accept_3_2 1 57 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 57 113))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 113
  (allA_succ_of_accept 55 56 113 (accept_3_2 55 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  56 113 (Polychromatic418967fa.accept_21_12_14_8_1_5258 54 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 56 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 113 (accept_3_2 52 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 56 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 113
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 113 (accept_3_2 49 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 113 (Polychromatic418967fa.accept_10_7_6_3_1_927 47 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 113 (accept_3_2 46 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 113
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 113 (accept_3_2 43 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 113 (Polychromatic418967fa.accept_16_9_8_1_1_1228 41 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 113 (accept_3_2 40 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 113
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 113 (accept_3_2 37 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 113 (Polychromatic418967fa.accept_16_4_8_1_1_5257 36 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 113 (accept_3_2 34 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 113
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 32 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 113 (accept_3_2 31 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 113 (Polychromatic418967fa.accept_10_9_6_3_1_545 29 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 113 (accept_3_2 28 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 113
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 113 (accept_3_2 25 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 113 (Polychromatic418967fa.accept_16_7_8_1_1_3061 23 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 113 (accept_3_2 22 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 113
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 20 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 113 (accept_3_2 19 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 113 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 113 (accept_3_2 16 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 113
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 113 (accept_3_2 13 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 113 (Polychromatic418967fa.accept_21_11_14_8_1_5256 11 56 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 113 (accept_3_2 10 56 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 113
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 113 (accept_3_2 7 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  113 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 113 (Polychromatic418967fa.accept_13_5_4_9_1_601 5 56 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 113 (accept_3_2 4 56 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 113 (Polychromatic418967fa.accept_11_2_1_3_1_683 2
  56 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 113 (accept_3_2 1 56 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 113))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 113 (allA_of_3_0 55 55 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 113
  (allA_succ_of_accept 53 54 113 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 113 (accept_3_2 52 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 113 (Polychromatic418967fa.accept_13_11_2_9_1_2640
  50 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 113 (accept_3_2 49
  54 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 113
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 113 (accept_3_2 46 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 54 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 113 (Polychromatic418967fa.accept_13_5_2_9_1_1195
  44 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 113 (accept_3_2 43
  54 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 113
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 42 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 113 (accept_3_2 40 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 113 (accept_3_2 37 54
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 113
  (Polychromatic418967fa.accept_17_2_3_11_1_2919 36 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 113 (accept_3_2 34 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 113 (Polychromatic418967fa.accept_13_7_2_9_1_1826 33 54 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 113 (Polychromatic418967fa.accept_7_4_5_1_1_418 32
  54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 113 (accept_3_2 31 54
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 113
  (Polychromatic418967fa.accept_21_9_12_8_1_5255 30 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 113 (Polychromatic418967fa.accept_10_9_4_3_1_539 29 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 113 (accept_3_2 28 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 113 (Polychromatic418967fa.accept_17_9_3_11_1_3983
  26 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 113 (accept_3_2 25
  54 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 113
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 113 (accept_3_2 22 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 113 (Polychromatic418967fa.accept_16_5_6_1_1_2118 21 54 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 20
  54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 113 (accept_3_2 19 54
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 113
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 113 (accept_3_2 16 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 113 (Polychromatic418967fa.accept_13_1_2_9_1_1186
  14 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 113 (accept_3_2 13
  54 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 113
  (Polychromatic418967fa.accept_24_12_6_17_1_5254 12 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 113 (accept_3_2 10 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 113 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 54 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 113 (Polychromatic418967fa.accept_19_8_16_18_1_5253
  8 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 113 (accept_3_2 7 54
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 113 (Polychromatic418967fa.accept_7_6_5_1_1_416
  6 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 113
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 54 113 (accept_3_2 4 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54
  113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 54 113 (Polychromatic418967fa.accept_15_2_9_8_1_736 2 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 113 (accept_3_2 1 54 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 54 113)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 113
  (allA_succ_of_accept 52 53 113 (accept_3_2 52 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  53 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 113 (Polychromatic418967fa.accept_11_6_9_3_1_1103 50 53 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 113 (accept_3_2 49 53 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 53 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 113
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 113 (accept_3_2 46 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 113 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 53 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 113 (accept_3_2 43 53 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 113
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 41 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 113 (accept_3_2 40 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 53 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 113 (accept_3_2 37 53 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 113 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 53 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 113
  (Polychromatic418967fa.accept_19_16_15_18_1_5252 35 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 53 113 (accept_3_2 34 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 53 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 53 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 113 (Polychromatic418967fa.accept_13_6_1_9_1_619 32 53 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 113 (accept_3_2 31 53 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 30
  53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 113
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 113 (accept_3_2 28 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 113 (Polychromatic418967fa.accept_22_5_9_3_1_5251 27 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 53 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 113 (accept_3_2 25 53 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 53 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 113
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 23 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 113 (accept_3_2 22 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 113 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 53 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 113 (accept_3_2 19 53 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 113 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 53 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 113
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 113 (accept_3_2 16 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 113 (Polychromatic418967fa.accept_19_14_15_18_1_5250 14 53 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 113 (accept_3_2 13 53 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 113
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 113 (accept_3_2 10 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 113 (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 113 (Polychromatic418967fa.accept_13_8_1_9_1_1178 8 53 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 113 (accept_3_2 7 53 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 53 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 113
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 113 (accept_3_2 4 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  113 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 53 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 113 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 53 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 113 (accept_3_2 1 53 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 113))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 113 (allA_of_3_0 52 52
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 113 (allA_succ_of_accept 50 51 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 113 (accept_3_2 49 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 113 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 113 (accept_3_2 46 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 51 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 113 (accept_3_2 43 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 113 (accept_3_2 40 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 51 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 113 (accept_3_2 37 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 113 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 113 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 113 (accept_3_2 34 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 113 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 51 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 113 (accept_3_2 31 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 113 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 113 (accept_3_2 28 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 51 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 113 (accept_3_2 25 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 113 (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 51 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 113 (accept_3_2 22 51 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 113 (accept_3_2 19 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 113 (accept_3_2 16 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 113 (Polychromatic418967fa.accept_11_4_7_3_1_289 15 51 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 113 (accept_3_2 13 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 113 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 113 (accept_3_2 10 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 113 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 51 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 113 (accept_3_2 7 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 113 (Polychromatic418967fa.accept_19_5_13_18_1_5249 5 51 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 113 (accept_3_2 4 51 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 51 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 113 (accept_3_2 1 51 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 113)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 113 (allA_succ_of_accept 49 50 113 (accept_3_2 49 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 113 (Polychromatic418967fa.accept_15_3_5_8_1_1387 48 50 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 113 (accept_3_2 46 50 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 113
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 113 (accept_3_2 43 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 113 (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 113 (Polychromatic418967fa.accept_11_8_6_3_1_661 41 50 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 113 (accept_3_2 40 50 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 113
  (Polychromatic418967fa.accept_16_6_2_1_1_4081 38 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 113 (accept_3_2 37 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 113 (Polychromatic418967fa.accept_19_17_12_18_1_5248 36 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 113 (accept_3_2 34 50 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 113
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 113 (accept_3_2 31 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 113 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 113 (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 50 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 113 (accept_3_2 28 50 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 113
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 113 (accept_3_2 25 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 113 (Polychromatic418967fa.accept_23_1_4_21_1_2177 24 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 113 (accept_3_2 22 50 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 113
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 113 (accept_3_2 19 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 113 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 113 (Polychromatic418967fa.accept_19_17_12_18_1_5248 17 50 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 113 (accept_3_2 16 50 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 113
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 113 (accept_3_2 13 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 113 (Polychromatic418967fa.accept_15_12_5_8_1_5247 12 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 113 (accept_3_2 10 50 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 113
  (Polychromatic418967fa.accept_11_8_6_3_1_661 8 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 113 (accept_3_2 7 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  113 (Polychromatic418967fa.accept_16_6_2_1_1_4081 6 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 50 113 (Polychromatic418967fa.accept_17_5_16_11_1_3998 5 50 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 113 (accept_3_2 4 50 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 113
  (Polychromatic418967fa.accept_13_2_11_9_1_591 2 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 113 (accept_3_2 1 50 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  113)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 113 (allA_of_3_0 49 49 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 113 (allA_succ_of_accept 47 48 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 47
  48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 113 (accept_3_2 46 48
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 113
  (Polychromatic418967fa.accept_10_5_8_3_1_229 45 48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 48 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 113 (accept_3_2 43 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 48 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 48 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 113 (Polychromatic418967fa.accept_10_1_8_3_1_947
  41 48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 113 (accept_3_2 40
  48 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 48 113
  (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 48 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 113 (accept_3_2 37 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 48 113 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 48 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 113 (Polychromatic418967fa.accept_9_8_3_5_1_241 35
  48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 113 (accept_3_2 34 48
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 48 113
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 48 113 (Polychromatic418967fa.accept_23_9_2_21_1_5246 32 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 113 (accept_3_2 31 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 48 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 48 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 29
  48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 113 (accept_3_2 28 48
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 48 113
  (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 48 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 113 (accept_3_2 25 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 48 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 48 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 23
  48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 113 (accept_3_2 22 48
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 48 113
  (Polychromatic418967fa.accept_10_1_8_3_1_947 21 48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 48 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 113 (accept_3_2 19 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 48 113 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 48 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 113 (Polychromatic418967fa.accept_9_8_3_5_1_241 17
  48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 113 (accept_3_2 16 48
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 113
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 48 113 (Polychromatic418967fa.accept_19_14_10_18_1_5244 14 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 113 (accept_3_2 13 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 48 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 48 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 11
  48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 113 (accept_3_2 10 48
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 48 113 (Polychromatic418967fa.accept_7_2_6_1_1_73
  9 48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 113
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 113 (accept_3_2 7 48 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48
  113 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 48 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 113 (accept_3_2 4 48 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 48 113 (Polychromatic418967fa.accept_17_3_14_11_1_5243 3 48 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 48
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 113 (accept_3_2 1 48 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 113)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 113 (allA_succ_of_accept 46 47 113 (accept_3_2 46 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 47 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 47 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 47 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 113 (accept_3_2 43 47 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 113
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 113 (accept_3_2 40 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 113 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 113 (accept_3_2 37 47 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 113 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 47 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 113
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 113 (accept_3_2 34 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 113 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 47 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 113 (accept_3_2 31 47 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 113
  (Polychromatic418967fa.accept_13_3_8_9_1_1134 29 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 113 (accept_3_2 28 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 113 (accept_3_2 25 47 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 47 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 113
  (Polychromatic418967fa.accept_17_6_13_11_1_995 23 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 113 (accept_3_2 22 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 47 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 113 (accept_3_2 19 47 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 113
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 113 (accept_3_2 16 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 113 (accept_3_2 13 47 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 113
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 113 (accept_3_2 10 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 113 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 47 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 113 (accept_3_2 7 47 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 113
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 113 (accept_3_2 4 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  113 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 47 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 113 (accept_3_2 1 47 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 113))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 113 (allA_of_3_0 46 46 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 113 (allA_succ_of_accept 44 45 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 113 (accept_3_2 43 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 113 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 113 (Polychromatic418967fa.accept_13_2_6_9_1_2636 41 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 113 (accept_3_2 40 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 45 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 113 (accept_3_2 37 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 113 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 113 (Polychromatic418967fa.accept_11_2_1_3_1_683 35 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 113 (accept_3_2 34 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 113 (accept_3_2 31 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 113 (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 113 (accept_3_2 28 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 113 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 45 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 113 (accept_3_2 25 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 113 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 113 (accept_3_2 22 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 113 (Polychromatic418967fa.accept_16_5_13_1_1_2084 21 45 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 113 (accept_3_2 19 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 113 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 113 (accept_3_2 16 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 113 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 45 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 113 (accept_3_2 13 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 113 (accept_3_2 10 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 113 (accept_3_2 7 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  113 (Polychromatic418967fa.accept_19_6_7_18_1_120 6 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 45 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 113 (accept_3_2 4 45 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 113 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 45 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 113 (accept_3_2 1 45 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  113))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 113 (allA_succ_of_accept 43 44 113 (accept_3_2 43 44
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 113
  (Polychromatic418967fa.accept_9_6_8_5_1_837 42 44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 113 (accept_3_2 40 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 38
  44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 113 (accept_3_2 37 44
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 113
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 113 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 113 (accept_3_2 34 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 113 (Polychromatic418967fa.accept_18_14_8_5_1_860
  32 44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 113 (accept_3_2 31
  44 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 113
  (Polychromatic418967fa.accept_9_3_8_5_1_65 30 44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 44 113 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 113 (accept_3_2 28 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 44 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 113 (Polychromatic418967fa.accept_12_2_8_5_1_408
  26 44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 113 (accept_3_2 25
  44 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 113
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 44 113 (Polychromatic418967fa.accept_20_3_4_13_1_3824 23 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 113 (accept_3_2 22 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 44 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 20
  44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 113 (accept_3_2 19 44
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 113
  (Polychromatic418967fa.accept_16_2_12_1_1_3086 18 44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 44 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 113 (accept_3_2 16 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 44 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 113 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 113 (accept_3_2 13
  44 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 113
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 44 113 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 113 (accept_3_2 10 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 44 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 113 (Polychromatic418967fa.accept_14_8_2_1_1_1652 8
  44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 113 (accept_3_2 7 44 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 6
  44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 113
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 113 (accept_3_2 4 44 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  113 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 113 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 113 (accept_3_2 1 44 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 113)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 113 (allA_of_3_0 43 43 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 113 (allA_succ_of_accept 41 42 113
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 41 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 113 (accept_3_2 40 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 113 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 42 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 113 (accept_3_2 37 42 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 113 (Polychromatic418967fa.accept_17_2_8_11_1_1041 36 42 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 113 (accept_3_2 34 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 113 (Polychromatic418967fa.accept_13_7_3_9_1_1142 33 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 113 (Polychromatic418967fa.accept_13_6_3_9_1_1827 32 42 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 113 (accept_3_2 31 42 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 42 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 113
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 113 (accept_3_2 28 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 113 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 42 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 113 (accept_3_2 25 42 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 113 (Polychromatic418967fa.accept_19_5_4_18_1_5242 24 42 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 113 (accept_3_2 22 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 113 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 42 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 113 (accept_3_2 19 42 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 113 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 42 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 113
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 113 (accept_3_2 16 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 113 (Polychromatic418967fa.accept_17_14_8_11_1_4052 14 42 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 113 (accept_3_2 13 42 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 42 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 113 (accept_3_2 10 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 113 (Polychromatic418967fa.accept_16_9_10_1_1_2998 9 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 42 113 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 42 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 113 (accept_3_2 7 42 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 113 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 42 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 113
  (Polychromatic418967fa.accept_10_5_2_3_1_239 5 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 113 (accept_3_2 4 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 113 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 42 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 113 (accept_3_2 1 42 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 113)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 113 (allA_succ_of_accept 40 41
  113 (accept_3_2 40 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 113
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 113 (Polychromatic418967fa.accept_10_8_1_3_1_1374 38 41 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 113 (accept_3_2 37 41 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 113 (Polychromatic418967fa.accept_25_11_16_13_1_2000 36 41 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 113
  (Polychromatic418967fa.accept_14_7_13_1_1_922 35 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 113 (accept_3_2 34 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 113 (Polychromatic418967fa.accept_10_2_1_3_1_233 32 41 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 113 (accept_3_2 31 41 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 41 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 113
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 113 (accept_3_2 28 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 113 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 41 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 113 (accept_3_2 25 41 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 113 (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 41 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 113
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 113 (accept_3_2 22 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 113 (Polychromatic418967fa.accept_14_7_13_1_1_922 21 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 113 (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 41 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 113 (accept_3_2 19 41 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 113 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 41 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 113
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 113 (accept_3_2 16 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 113 (Polychromatic418967fa.accept_19_15_3_18_1_5241 15 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 113 (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 41 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 113 (accept_3_2 13 41 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 41 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 113
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 113 (accept_3_2 10 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 113 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 41 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 113 (accept_3_2 7 41 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 113 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 41 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 113
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 113 (accept_3_2 4 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  113 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 41 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 41 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 41 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 113 (accept_3_2 1 41 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 41 113))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 113 (allA_of_3_0 40 40
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 113 (allA_succ_of_accept 38 39 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 113 (accept_3_2 37 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 113 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 113 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 39 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 113 (accept_3_2 34 39 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 39 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 113 (accept_3_2 31 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 39 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 113 (accept_3_2 28 39 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 113 (Polychromatic418967fa.accept_19_8_1_18_1_5240 27 39 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 113 (accept_3_2 25 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 113 (Polychromatic418967fa.accept_17_6_5_11_1_4073 23 39 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 113 (accept_3_2 22 39 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 113 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 39 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 113 (accept_3_2 19 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 39 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 113 (accept_3_2 16 39 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 113 (accept_3_2 13 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 39 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 113 (accept_3_2 10 39 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 113 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 39 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 113 (accept_3_2 7 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 39 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 113 (accept_3_2 4 39 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 113 (accept_3_2 1 39 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 113))))))))))))))))))))))))))))))))))))))) (allB_succ 38 113
  (allA_succ_of_accept 37 38 113 (accept_3_2 37 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 113 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 113 (accept_3_2 34 38 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 113
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 113 (accept_3_2 31 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 113 (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 38 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 113 (accept_3_2 28 38 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 113
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 113 (accept_3_2 25 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 113 (accept_3_2 22 38 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 113
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 113 (accept_3_2 19 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 113 (accept_3_2 16 38 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 113
  (Polychromatic418967fa.accept_21_14_17_8_1_5239 14 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 113 (accept_3_2 13 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 113 (accept_3_2 10 38 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 113
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 113 (accept_3_2 7 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  113 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 38 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 38 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 113 (accept_3_2 4 38 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 38
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 113 (accept_3_2 1 38 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 113)))))))))))))))))))))))))))))))))))))) (allB_succ 37 113
  (allA_of_3_0 37 37 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 113 (allA_succ_of_accept 35 36 113
  (Polychromatic418967fa.accept_14_7_8_1_1_1621 35 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 113 (accept_3_2 34 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 113 (Polychromatic418967fa.accept_21_12_15_8_1_5238 33 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 113 (Polychromatic418967fa.accept_13_6_10_9_1_4329 32 36 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 113 (accept_3_2 31 36 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 113 (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 36 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 113
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 113 (accept_3_2 28 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 113 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 113 (Polychromatic418967fa.accept_17_9_2_11_1_4042 26 36 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 113 (accept_3_2 25 36 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 113 (Polychromatic418967fa.accept_16_8_4_1_1_2102 24 36 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 113
  (Polychromatic418967fa.accept_14_9_8_1_1_2381 23 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 113 (accept_3_2 22 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 113 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 113 (Polychromatic418967fa.accept_17_3_2_11_1_1895 20 36 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 113 (accept_3_2 19 36 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 113 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 36 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 113
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 113 (accept_3_2 16 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 113 (Polychromatic418967fa.accept_22_15_14_3_1_5237 15 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 113 (Polychromatic418967fa.accept_13_1_10_9_1_215 14 36 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 113 (accept_3_2 13 36 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 113 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 36 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 113
  (Polychromatic418967fa.accept_19_11_17_18_1_5236 11 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 36 113 (accept_3_2 10 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 36 113 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 36 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 113 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 36 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 113 (accept_3_2 7 36 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 113 (Polychromatic418967fa.accept_13_6_10_9_1_4329
  6 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 113
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 113 (accept_3_2 4 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  113 (Polychromatic418967fa.accept_16_3_4_1_1_2996 3 36 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 36 113 (Polychromatic418967fa.accept_14_2_8_1_1_1647 2 36 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 113 (accept_3_2 1 36 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 36 113)))))))))))))))))))))))))))))))))))) (allB_succ 35 113 (allA_succ_of_accept 34 35
  113 (accept_3_2 34 35 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 113
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 35 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 113 (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 35 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 113 (accept_3_2 31 35 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 113 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  35 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 113 (accept_3_2 28 35
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 113
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 35 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 113 (accept_3_2 25 35 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 113 (Polychromatic418967fa.accept_11_1_2_3_1_688
  23 35 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 113 (accept_3_2 22
  35 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 113
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 35 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 113 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 35 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 113 (accept_3_2 19 35 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 113 (Polychromatic418967fa.accept_10_7_5_3_1_542
  17 35 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 113 (accept_3_2 16
  35 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 113
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 35 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 113 (accept_3_2 13 35 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 113 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  35 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 113 (accept_3_2 10 35
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 113
  (Polychromatic418967fa.accept_19_9_16_18_1_3887 9 35 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 113 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 35 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 113 (accept_3_2 7 35 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 113 (Polychromatic418967fa.accept_20_5_15_13_1_5235
  5 35 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 113 (accept_3_2 4 35
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 113 (Polychromatic418967fa.accept_9_3_8_5_1_65
  3 35 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 113 (accept_3_2 1 35 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  113))))))))))))))))))))))))))))))))))) (allB_succ 34 113 (allA_of_3_0 34 34 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 113 (allA_succ_of_accept 32 33 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 113 (accept_3_2 31 33 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 30
  33 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 113
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 113 (accept_3_2 28 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 113 (accept_3_2 25 33 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 113
  (Polychromatic418967fa.accept_19_4_14_18_1_5234 23 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 113 (accept_3_2 22 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 113 (accept_3_2 19 33 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 113 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 33 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 113
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 113 (accept_3_2 16 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 113 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 113 (accept_3_2 13 33 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 113
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 113 (accept_3_2 10 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 113 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 113 (accept_3_2 7 33 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 33 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 113
  (Polychromatic418967fa.accept_15_5_3_8_1_748 5 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 113 (accept_3_2 4 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  113 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 33 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 113 (accept_3_2 1 33 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 113))))))))))))))))))))))))))))))))) (allB_succ 32 113 (allA_succ_of_accept 31 32 113
  (accept_3_2 31 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 113
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 113 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 32 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 113 (accept_3_2 28 32 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 26
  32 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 113 (accept_3_2 25 32
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 113 (Polychromatic418967fa.accept_7_3_4_1_1_71
  24 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 32 113
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 32 113 (accept_3_2 22 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  32 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 32 113 (Polychromatic418967fa.accept_13_7_6_9_1_1831 20 32 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 113 (accept_3_2 19 32 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 113 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 32 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 113
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 32 113 (accept_3_2 16 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  32 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 32 113 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 32 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 113 (accept_3_2 13 32 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 32 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 113
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 32 113 (accept_3_2 10 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  32 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 32 113 (Polychromatic418967fa.accept_18_8_14_5_1_2778 8 32 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 113 (accept_3_2 7 32 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 113 (Polychromatic418967fa.accept_15_6_2_8_1_2223 6 32 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 113
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 113 (accept_3_2 4 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  113 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 113 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 32 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 113 (accept_3_2 1 32 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 113)))))))))))))))))))))))))))))))) (allB_succ 31 113 (allA_of_3_0 31 31 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 113 (allA_succ_of_accept 29 30 113
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 113 (accept_3_2 28 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 113 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 30 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 113 (accept_3_2 25 30 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 30 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 113 (accept_3_2 22 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 113 (Polychromatic418967fa.accept_13_8_4_9_1_1145 21 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 30 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 113 (accept_3_2 19 30 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 113 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 30 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 113
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 113 (accept_3_2 16 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 113 (Polychromatic418967fa.accept_23_14_7_21_1_5233 14 30 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 113 (accept_3_2 13 30 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 113 (Polychromatic418967fa.accept_17_12_13_11_1_2910 12 30
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 113 (accept_3_2 10 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 113 (Polychromatic418967fa.accept_18_9_12_5_1_864 9 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 30 113 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 30 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 113 (accept_3_2 7 30 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 30 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 113
  (Polychromatic418967fa.accept_11_5_8_3_1_66 5 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 113 (accept_3_2 4 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 30 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 113 (accept_3_2 1 30 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 113)))))))))))))))))))))))))))))) (allB_succ 29 113 (allA_succ_of_accept 28 29 113
  (accept_3_2 28 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 113
  (Polychromatic418967fa.accept_19_8_10_18_1_5232 27 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 29 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 113 (accept_3_2 25 29 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 29 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 113
  (Polychromatic418967fa.accept_17_6_12_11_1_5231 23 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 113 (accept_3_2 22 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 113 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 113 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 29 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 113 (accept_3_2 19 29 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 113 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 29 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 113
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 113 (accept_3_2 16 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 113 (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 29 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 113 (accept_3_2 13 29 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 113 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 29 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 113
  (Polychromatic418967fa.accept_19_11_10_18_1_5230 11 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 29 113 (accept_3_2 10 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 29 113 (Polychromatic418967fa.accept_15_9_14_8_1_1396 9 29 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 113 (accept_3_2 7 29 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  29 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 113
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 5 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 113 (accept_3_2 4 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  113 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 29 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 113 (Polychromatic418967fa.accept_13_2_3_9_1_2610 2 29 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 113 (accept_3_2 1 29 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 113))))))))))))))))))))))))))))) (allB_succ 28 113 (allA_of_3_0 28 28 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 113 (allA_succ_of_accept 26 27 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 113 (accept_3_2 25 27 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 113 (Polychromatic418967fa.accept_10_4_7_3_1_54 24
  27 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 113
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 27 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 113 (accept_3_2 22 27 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 113 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 27 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 113 (accept_3_2 19 27 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 113
  (Polychromatic418967fa.accept_22_17_5_3_1_5229 17 27 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 113 (accept_3_2 16 27 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 113 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 27 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 113 (accept_3_2 13 27 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 113
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 27 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 113 (accept_3_2 10 27 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 27 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 27 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 113 (accept_3_2 7 27 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 113
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 27 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 113 (accept_3_2 4 27 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  113 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 27 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 27 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 113 (accept_3_2 1 27 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 27 113))))))))))))))))))))))))))) (allB_succ 26 113 (allA_succ_of_accept 25 26 113
  (accept_3_2 25 26 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 113
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 26 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 113 (accept_3_2 22 26 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 20
  26 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 113 (accept_3_2 19 26
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 113
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 26 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 26 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 113 (accept_3_2 16 26 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 113 (Polychromatic418967fa.accept_18_14_8_5_1_860
  14 26 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 113 (accept_3_2 13
  26 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 113
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 26 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 26 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 113 (accept_3_2 10 26 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 26 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 113 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8
  26 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 113 (accept_3_2 7 26 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 113 (Polychromatic418967fa.accept_7_6_5_1_1_416 6
  26 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 113
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 26 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 113 (accept_3_2 4 26 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 113 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 26 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 113 (accept_3_2 1 26 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 113)))))))))))))))))))))))))) (allB_succ 25 113 (allA_of_3_0 25 25 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 113 (allA_succ_of_accept 23 24 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 113 (accept_3_2 22 24 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 21
  24 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 113
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 24 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 113 (accept_3_2 19 24 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 24 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 113 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 113 (accept_3_2 16 24 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 113 (Polychromatic418967fa.accept_13_2_11_9_1_591 15 24 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 113
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 24 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 113 (accept_3_2 13 24 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 24 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 113 (accept_3_2 10 24 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 113
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 24 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 113 (accept_3_2 7 24 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  113 (Polychromatic418967fa.accept_19_6_5_18_1_5228 6 24 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 24 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 113 (accept_3_2 4 24 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 113
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 24 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 113 (accept_3_2 1 24 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  113)))))))))))))))))))))))) (allB_succ 23 113 (allA_succ_of_accept 22 23 113 (accept_3_2 22 23 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 113 (Polychromatic418967fa.accept_17_4_6_11_1_1030 21 23 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 113
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 23 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 113 (accept_3_2 19 23 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 23 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 113 (accept_3_2 16 23 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 113 (Polychromatic418967fa.accept_19_15_4_18_1_5227 15 23 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 113 (accept_3_2 13 23 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 113 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 23 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 113 (Polychromatic418967fa.accept_19_11_4_18_1_5226 11 23 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 113 (accept_3_2 10 23 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 113 (Polychromatic418967fa.accept_22_9_1_3_1_5225 9 23 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 113
  (Polychromatic418967fa.accept_14_8_9_1_1_3313 8 23 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 113 (accept_3_2 7 23 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 113 (Polychromatic418967fa.accept_17_5_6_11_1_3974 5 23 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 113 (accept_3_2 4 23 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 23 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 113 (accept_3_2 1 23 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 113))))))))))))))))))))))) (allB_succ 22 113 (allA_of_3_0 22 22
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 113 (allA_succ_of_accept 20 21 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 113 (accept_3_2 19 21 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 113 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 21 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 113 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 21 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 113 (accept_3_2 16 21 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 113 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 113 (accept_3_2 13 21 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 113 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 21 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 113 (accept_3_2 10 21 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 113 (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 21 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 113 (accept_3_2 7 21 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  113 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 113 (Polychromatic418967fa.accept_19_5_2_18_1_2716 5 21 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 113 (accept_3_2 4 21 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 113 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 113 (accept_3_2 1 21 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 113))))))))))))))))))))) (allB_succ 20 113 (allA_succ_of_accept
  19 20 113 (accept_3_2 19 20 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 113
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 20 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 20 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 113 (accept_3_2 16 20 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 113 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 20 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 113 (accept_3_2 13
  20 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 113
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 20 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 113 (Polychromatic418967fa.accept_13_11_7_9_1_612 11 20 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 113 (accept_3_2 10 20 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 8
  20 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 113 (accept_3_2 7 20 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 113 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  20 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 113
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 20 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 113 (accept_3_2 4 20 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  113 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 20 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 113 (accept_3_2 1 20 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 113)))))))))))))))))))) (allB_succ 19 113 (allA_of_3_0 19 19 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 113 (allA_succ_of_accept 17 18 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 18 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 113 (accept_3_2 16 18 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  18 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 113
  (Polychromatic418967fa.accept_13_1_5_9_1_226 14 18 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 113 (accept_3_2 13 18 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 18 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 113 (accept_3_2 10 18 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 113 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 18 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 113
  (Polychromatic418967fa.accept_17_8_1_11_1_4004 8 18 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 113 (accept_3_2 7 18 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  113 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 18 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 18 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 113 (accept_3_2 4 18 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 113 (Polychromatic418967fa.accept_13_2_5_9_1_610 2
  18 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 113 (accept_3_2 1 18 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 113)))))))))))))))))) (allB_succ 17 113 (allA_succ_of_accept 16
  17 113 (accept_3_2 16 17 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 113
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 17 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 113 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 17 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 113 (accept_3_2 13 17 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 113 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  17 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 113 (accept_3_2 10 17
  113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 113 (Polychromatic418967fa.accept_7_2_3_1_1_10
  9 17 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 113
  (Polychromatic418967fa.accept_11_8_6_3_1_661 8 17 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 113 (accept_3_2 7 17 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  113 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 17 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 113 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 113 (accept_3_2 4 17 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 113 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 17 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 113 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 17
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 113 (accept_3_2 1 17 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 113))))))))))))))))) (allB_succ 16 113 (allA_of_3_0 16 16 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 113 (allA_succ_of_accept 14 15 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 113 (accept_3_2 13 15 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 15 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 113 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 15 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 113 (accept_3_2 10 15 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 113 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 15 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 113 (accept_3_2 7 15 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 113 (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 15 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 113 (accept_3_2 4 15 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 113 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 15 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 113 (accept_3_2 1 15 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 113))))))))))))))) (allB_succ 14 113 (allA_succ_of_accept 13 14
  113 (accept_3_2 13 14 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 113
  (Polychromatic418967fa.accept_17_12_14_11_1_998 12 14 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 113 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 113 (accept_3_2 10 14 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 14 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 113 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  14 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 113 (accept_3_2 7 14 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 113 (Polychromatic418967fa.accept_13_6_1_9_1_619 6
  14 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 113
  (Polychromatic418967fa.accept_13_5_1_9_1_618 5 14 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 113 (accept_3_2 4 14 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  113 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 113 (Polychromatic418967fa.accept_13_2_1_9_1_1174 2 14 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 113 (accept_3_2 1 14 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 113)))))))))))))) (allB_succ 13 113 (allA_of_3_0 13 13 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 113 (allA_succ_of_accept 11 12 113 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 113 (accept_3_2 10 12 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 113 (Polychromatic418967fa.accept_18_9_12_5_1_864 9
  12 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 113
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 12 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 113 (accept_3_2 7 12 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  113 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 12 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 113 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 113 (accept_3_2 4 12 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 113 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 12
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 113 (accept_3_2 1 12 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 113)))))))))))) (allB_succ 11 113 (allA_succ_of_accept 10 11 113
  (accept_3_2 10 11 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 113
  (Polychromatic418967fa.accept_22_9_11_3_1_5224 9 11 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 113 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 113 (accept_3_2 7 11 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 113 (Polychromatic418967fa.accept_7_5_4_1_1_412 5
  11 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 113 (accept_3_2 4 11 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 113 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 11
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 113
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 113 (accept_3_2 1 11 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  113))))))))))) (allB_succ 10 113 (allA_of_3_0 10 10 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 113
  (allA_succ_of_accept 8 9 113 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 113 (accept_3_2 7 9 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 113 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 9 113 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 113 (Polychromatic418967fa.accept_16_5_9_1_1_2070 5
  9 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 113 (accept_3_2 4 9 113
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 113 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 9
  113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 113
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 113 (accept_3_2 1 9 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 113)))))))))
  (allB_succ 8 113 (allA_succ_of_accept 7 8 113 (accept_3_2 7 8 113 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 113 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 8 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 113 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 8 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 113 (accept_3_2 4 8 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 113 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 113
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 8 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 113 (accept_3_2 1 8 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 113))))))))
  (allB_succ 7 113 (allA_of_3_0 7 7 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 113 (allA_succ_of_accept 5
  6 113 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 6 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 113 (accept_3_2 4 6 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 113
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 113 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 6 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 113 (accept_3_2 1 6 113 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 113)))))) (allB_succ 5 113 (allA_succ_of_accept 4 5 113 (accept_3_2 4 5 113 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 113 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 5 113
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 113
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 5 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 113 (accept_3_2 1 5 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 113)))))
  (allB_succ 4 113 (allA_of_3_0 4 4 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 113 (allA_succ_of_accept 2
  3 113 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 113 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 113 (accept_3_2 1 3 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 113)))
  (allB_succ 2 113 (allA_succ_of_accept 1 2 113 (accept_3_2 1 2 113 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  113)) (allB_two
  113)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


