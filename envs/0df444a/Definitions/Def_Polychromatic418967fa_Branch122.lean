-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch122
-- name    : Polychromatic418967fa_Branch122
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:12:30.12536+00:00
-- url     : https://prove2.me/theorems/105fc65f-964f-48c4-8cc7-253c52eaca5b
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

def Polychromatic418967fa.branch_122 : allB 122 122 :=
  allB_succ' 2 121 122 (Eq.refl Bool.true) (allA_of_3_0 2 121 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  120 122 (Eq.refl Bool.true) (allA_succ_of_gcd 2 120 122 2 1 60 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 122 (accept_3_2 1 120 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 120 122))) (allB_succ' 4 119 122 (Eq.refl Bool.true) (allA_succ_of_accept 3 119 122
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 119 122 (Polychromatic418967fa.accept_18_2_11_14_1_69 2 119 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 122 (accept_3_2 1 119 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 119 122)))) (allB_succ' 5 118 122 (Eq.refl Bool.true) (allA_of_3_0 5 118 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 117 122 (Eq.refl Bool.true) (allA_succ_of_accept 5 117 122
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 122 (accept_3_2 4 117 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 117 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 122 (accept_3_2 1 117 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117 122)))))) (allB_succ' 7 116 122 (Eq.refl Bool.true) (allA_succ_of_gcd 6 116 122 2 3
  58 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 122
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 116 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 116 122 2 2 58 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 116 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 116 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 122 2 1 58 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 122 (accept_3_2 1 116 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 116 122))))))) (allB_succ' 8 115 122 (Eq.refl Bool.true) (allA_of_3_0 8 115 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 114 122 (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 122 2 4 57 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 122
  (accept_3_2 7 114 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 122 2 3 57 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 122
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 114 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 114 122 2 2 57 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 114 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 114 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 122 2 1 57 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 122 (accept_3_2 1 114 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 114 122))))))))) (allB_succ' 10 113 122 (Eq.refl Bool.true) (allA_succ_of_accept 9 113 122
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 113 122 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 113 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 122 (accept_3_2 7 113 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 113 122 (Polychromatic418967fa.accept_15_6_8_2_1_104 6 113 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 5
  113 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 122 (accept_3_2 4 113
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 122 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 113 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 122
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 113 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 122 (accept_3_2 1 113 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  122)))))))))) (allB_succ' 11 112 122 (Eq.refl Bool.true) (allA_of_3_0 11 112 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 111 122 (Eq.refl Bool.true) (allA_succ_of_accept 11 111 122
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 122 (accept_3_2 10 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 122 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 111 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 122 (accept_3_2 7 111 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 122 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 111 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 122
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 122 (accept_3_2 4 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 122 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 111 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 111 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 122 (accept_3_2 1 111 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 122)))))))))))) (allB_succ' 13 110 122 (Eq.refl Bool.true) (allA_succ_of_gcd 12 110
  122 2 6 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  110 122 (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 110 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 110 122 2 5 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 110 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 110 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 122 2 4 55 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 122 (accept_3_2 7 110 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110 122 2 3 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 110 122 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 110
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 122 2 2 55 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 122
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 110 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 110 122 2 1 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 110 122 (accept_3_2 1 110 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  122))))))))))))) (allB_succ' 14 109 122 (Eq.refl Bool.true) (allA_of_3_0 14 109 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 108 122 (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 122 2 7 54 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 122 (accept_3_2 13 108 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 122 2 6 54 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 122
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 11 108 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 108 122 2 5 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 108 122 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 108 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 122 2 4 54 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 122 (accept_3_2 7 108 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 122 2 3 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 122 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 108 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 122 2 2 54 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 122
  (Polychromatic418967fa.accept_16_3_12_10_1_315 3 108 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 108 122 2 1 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 122 (accept_3_2 1 108 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  122))))))))))))))) (allB_succ' 16 107 122 (Eq.refl Bool.true) (allA_succ_of_accept 15 107 122
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 107 122 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 107 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 122 (accept_3_2 13 107 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 107 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 107 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 122 (Polychromatic418967fa.accept_9_2_8_5_1_228
  11 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 122 (accept_3_2 10
  107 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 122
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 107 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 107 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 122 (accept_3_2 7 107 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 107 122 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 107 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5
  107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 122 (accept_3_2 4 107
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 122 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 122
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 122 (accept_3_2 1 107 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  122)))))))))))))))) (allB_succ' 17 106 122 (Eq.refl Bool.true) (allA_of_3_0 17 106 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 105 122 (Eq.refl Bool.true) (allA_succ_of_accept 17 105 122
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 122 (accept_3_2 16 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 122 (Polychromatic418967fa.accept_22_14_17_12_1_5950 14 105 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 122 (accept_3_2 13 105 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 105 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 122 (accept_3_2 10 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 122 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 122 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 105 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 122 (accept_3_2 7 105 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 122 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 105 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 122
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 122 (accept_3_2 4 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 122 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 105 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 122 (accept_3_2 1 105 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105 122)))))))))))))))))) (allB_succ' 19 104 122 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 104 122 2 9 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 122 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 104 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 122 2 8 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 122 (Polychromatic418967fa.accept_20_15_4_2_1_5914
  15 104 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 122 2 7 52 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 122
  (accept_3_2 13 104 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 122 2 6 52 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 122
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 104 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 122 2 5 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 104 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 122 2 4 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 122 (accept_3_2 7 104 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 122 2 3 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 122 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 104 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 122 2 2 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 122 (Polychromatic418967fa.accept_14_3_6_10_1_752 3
  104 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 122 2 1 52 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 122 (accept_3_2 1
  104 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104 122))))))))))))))))))) (allB_succ' 20 103 122 (Eq.refl
  Bool.true) (allA_of_3_0 20 103 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 102 122 (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 102 122 2 10 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 122 (accept_3_2 19 102 122 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 122 2 9 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 122 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 102 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 122 2 8 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  102 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 122 2 7 51 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 122 (accept_3_2 13
  102 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 122 2 6 51 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 122
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 102 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 122 2 5 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 102 122 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 102 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 122 2 4 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 122 (accept_3_2 7 102 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 102 122 2 3 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 102 122 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 102 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 122 2 2 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 122 (Polychromatic418967fa.accept_12_3_6_2_1_747 3
  102 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 122 2 1 51 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 122 (accept_3_2 1
  102 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 122))))))))))))))))))))) (allB_succ' 22 101 122
  (Eq.refl Bool.true) (allA_succ_of_accept 21 101 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 122
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 122 (accept_3_2 19 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 122 (Polychromatic418967fa.accept_27_18_20_14_1_5949 18 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 122 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 101 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 122 (accept_3_2 16 101 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 122
  (Polychromatic418967fa.accept_11_3_2_1_1_994 14 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 122 (accept_3_2 13 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 122 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 122 (accept_3_2 10 101 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 122
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 122 (accept_3_2 7 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 122 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 101 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 122 (accept_3_2 4 101 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 122
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 2 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 122 (accept_3_2 1 101 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  122)))))))))))))))))))))) (allB_succ' 23 100 122 (Eq.refl Bool.true) (allA_of_3_0 23 100 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 24 99 122 (Eq.refl Bool.true) (allA_succ_of_accept 23 99 122
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 122 (accept_3_2 22 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 122 (Polychromatic418967fa.accept_25_20_24_22_1_5948 20 99 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 122 (accept_3_2 19 99 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 122 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 99 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 122
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 122 (accept_3_2 16 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 122 (Polychromatic418967fa.accept_17_15_14_3_1_5947 15 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 122 (Polychromatic418967fa.accept_13_1_8_5_1_2315 14 99 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 122 (accept_3_2 13 99 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 99 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 122
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 122 (accept_3_2 10 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 122 (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 99 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 122 (accept_3_2 7 99 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 122 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 99 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 122 (accept_3_2 4 99 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 122 (Polychromatic418967fa.accept_13_3_8_5_1_974 3
  99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 122
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 122 (accept_3_2 1 99 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  122)))))))))))))))))))))))) (allB_succ' 25 98 122 (Eq.refl Bool.true) (allA_succ_of_gcd 24 98 122 2 12 49 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 98 122
  (Polychromatic418967fa.accept_18_5_8_14_1_1282 23 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 98 122 2 11 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 98 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 98 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 122 2 10 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 122 (accept_3_2 19 98 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 122 2 9 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 98 122 (Polychromatic418967fa.accept_19_17_3_8_1_5946 17 98 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 122 2 8 49 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 122
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 122 2 7 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 122 (accept_3_2 13 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  122 2 6 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 122 2 5 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 122 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 98 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 122 2 4 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 122 (accept_3_2 7 98 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 122 2 3 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 122 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 98 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 122 2 2 49 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 122
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 122 2 1 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 122 (accept_3_2 1 98 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  122))))))))))))))))))))))))) (allB_succ' 26 97 122 (Eq.refl Bool.true) (allA_of_3_0 26 97 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 96 122 (Eq.refl Bool.true) (allA_succ_of_gcd 26 96 122 2 13 48 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 122 (accept_3_2 25
  96 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 122 2 12 48 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 122
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 96 122 2 11 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 96 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 122 2 10 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 122 (accept_3_2 19 96 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 122 2 9 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 96 122 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 96 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 122 2 8 48 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 122
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 96 122 2 7 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 122 (accept_3_2 13 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96
  122 2 6 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  96 122 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 96 122 2 5 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 96 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 122 2 4 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 122 (accept_3_2 7 96 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 122 2 3 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 96 122 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 96 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 122 2 2 48 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96 122
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 122 2 1 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 122 (accept_3_2 1 96 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  122))))))))))))))))))))))))))) (allB_succ' 28 95 122 (Eq.refl Bool.true) (allA_succ_of_accept 27 95 122
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 95 122 (Polychromatic418967fa.accept_15_11_5_2_1_520 26 95 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 122 (accept_3_2 25 95 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 95 122 (Polychromatic418967fa.accept_17_7_10_3_1_1421 24 95 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 122
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 122 (accept_3_2 22 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 122 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 95 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 122 (accept_3_2 19 95 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 122 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 95 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 122
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 122 (accept_3_2 16 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 122 (Polychromatic418967fa.accept_13_1_4_5_1_113 14 95 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 122 (accept_3_2 13 95 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 122 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 95 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 122
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 122 (accept_3_2 10 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 95 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 95 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 122 (accept_3_2 7 95 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 95 122 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 95 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 122 (accept_3_2 4 95 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 122
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 2 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 122 (accept_3_2 1 95 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  122)))))))))))))))))))))))))))) (allB_succ' 29 94 122 (Eq.refl Bool.true) (allA_of_3_0 29 94 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 93 122 (Eq.refl Bool.true) (allA_succ_of_accept 29 93 122
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 122 (accept_3_2 28 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  93 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 93 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 93 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 122 (accept_3_2 25 93 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 122 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 93 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 122 (accept_3_2 22 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  93 122 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 122 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 93 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 122 (accept_3_2 19 93 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 122 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 93 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 122
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 122 (accept_3_2 16 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  93 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 93 122 (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 93 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 122 (accept_3_2 13 93 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 122 (accept_3_2 10 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 122 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 93 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 122 (accept_3_2 7 93 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 122 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 93 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 122
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 122 (accept_3_2 4 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 122 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 93 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 122 (accept_3_2 1 93 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 93 122)))))))))))))))))))))))))))))) (allB_succ' 31 92 122 (Eq.refl Bool.true) (allA_succ_of_gcd
  30 92 122 2 15 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 92 122 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 92 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 92 122 2 14 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 122
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 27 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 92 122 2 13 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 92 122 (accept_3_2 25 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 92 122 2 12 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 92 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 92 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 122 2 11 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 122 (Polychromatic418967fa.accept_9_3_2_5_1_234 21
  92 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 122 2 10 46 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 122 (accept_3_2 19
  92 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 122 2 9 46 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 92 122
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 92 122 2 8 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 92 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 92 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 122 2 7 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 122 (accept_3_2 13 92 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 92 122 2 6 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 92 122 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 92 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 122 2 5 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 92
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 122 2 4 46 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 122 (accept_3_2 7 92
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 122 2 3 46 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92 122
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 92 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 122 2 2 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 122 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 92 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 122 2 1 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 122 (accept_3_2 1 92 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 122))))))))))))))))))))))))))))))) (allB_succ' 32 91 122 (Eq.refl Bool.true) (allA_of_3_0 32
  91 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 90 122 (Eq.refl Bool.true) (allA_succ_of_gcd 32 90 122
  2 16 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90
  122 (accept_3_2 31 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 122 2 15 45 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 122
  (Polychromatic418967fa.accept_43_29_4_36_1_5945 29 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 90 122 2 14 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 90 122 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 90 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 122 2 13 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 122 (accept_3_2 25 90 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 122 2 12 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 90 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 122 2 11 45 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 122
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 122 2 10 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 122 (accept_3_2 19 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90
  122 2 9 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  90 122 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 90 122 2 8 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 90 122 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 90 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 122 2 7 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 122 (accept_3_2 13 90 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 122 2 6 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 90 122 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 90 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 122 2 5 45 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 122
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 122 2 4 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 122 (accept_3_2 7 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 122
  2 3 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90
  122 (Polychromatic418967fa.accept_19_5_14_8_1_5944 5 90 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 90 122 2 2 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 90 122 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 90 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 122 2 1 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 122 (accept_3_2 1 90 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 90 122))))))))))))))))))))))))))))))))) (allB_succ' 34 89 122 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 89 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 122 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 89 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 122 (accept_3_2 31 89 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 30
  89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 122
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 122 (accept_3_2 28 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 122 (Polychromatic418967fa.accept_14_12_5_10_1_2130 26 89 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 122 (accept_3_2 25 89 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 122 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 89 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 122 (accept_3_2 22 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 89 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 122 (accept_3_2 19 89 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 122 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 89 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 122
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 122 (accept_3_2 16 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 122 (Polychromatic418967fa.accept_19_14_13_8_1_5943 14 89 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 122 (accept_3_2 13 89 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 122 (accept_3_2 10 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 122 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 89 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 122 (accept_3_2 7 89 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 122 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 89 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 122
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 122 (accept_3_2 4 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 89 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 122 (accept_3_2 1 89 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 122)))))))))))))))))))))))))))))))))) (allB_succ' 35 88 122 (Eq.refl Bool.true) (allA_of_3_0
  35 88 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 87 122 (Eq.refl Bool.true) (allA_succ_of_accept 35
  87 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 87 122 (accept_3_2 34 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 87 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 122 (Polychromatic418967fa.accept_20_12_7_2_1_4448 32 87
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 122 (accept_3_2 31 87 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 30
  87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 122
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 122 (accept_3_2 28 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 122 (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 122 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 87 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 122 (accept_3_2 25 87 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 122 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 87 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 122
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 122 (accept_3_2 22 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 122 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 87 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 122 (accept_3_2 19 87 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 122 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 87 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 122
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 122 (accept_3_2 16 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 122 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 122 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 87 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 122 (accept_3_2 13 87 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 87 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 122
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 122 (accept_3_2 10 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 122 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 122 (accept_3_2 7 87 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 87 122 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 87 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 122 (accept_3_2 4 87 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 122
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 122 (accept_3_2 1 87 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  122)))))))))))))))))))))))))))))))))))) (allB_succ' 37 86 122 (Eq.refl Bool.true) (allA_succ_of_gcd 36 86 122 2 18 43
  61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 122
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 86 122 2 17 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 86 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 86 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 86 122 2 16 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 86 122 (accept_3_2 31 86 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86 122 2 15 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 86 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 86 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 122 2 14 43 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 122
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 122 2 13 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 86 122 (accept_3_2 25 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86
  122 2 12 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  86 122 (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 86 122 2 11 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 86 122 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 86 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 122 2 10 43 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 122 (accept_3_2 19 86 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 122 2 9 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 86 122 (Polychromatic418967fa.accept_19_17_10_8_1_5942
  17 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 122 2 8 43 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 122
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 122 2 7 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 122 (accept_3_2 13 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  122 2 6 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 122 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 122 2 5 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 122 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 86 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 122 2 4 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 122 (accept_3_2 7 86 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 122 2 3 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 86 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 122 2 2 43 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 122
  (Polychromatic418967fa.accept_13_3_8_5_1_974 3 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 122 2 1 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 122 (accept_3_2 1 86 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  122))))))))))))))))))))))))))))))))))))) (allB_succ' 38 85 122 (Eq.refl Bool.true) (allA_of_3_0 38 85 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 84 122 (Eq.refl Bool.true) (allA_succ_of_gcd 38 84 122 2 19 42 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 122
  (accept_3_2 37 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 122 2 18 42 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 122
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 84 122 2 17 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 84 122 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 84 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 122 2 16 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 122 (accept_3_2 31 84 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 122 2 15 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 122 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 84 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 122 2 14 42 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 122
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 84 122 2 13 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 84 122 (accept_3_2 25 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84
  122 2 12 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  84 122 (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 84 122 2 11 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 84 122 (Polychromatic418967fa.accept_17_4_16_3_1_4620 21 84 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 84 122 2 10 42 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 122 (accept_3_2 19 84 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 122 2 9 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 122 (Polychromatic418967fa.accept_9_8_3_5_1_241 17
  84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 122 2 8 42 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 122
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 84 122 2 7 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 84 122 (accept_3_2 13 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84
  122 2 6 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  84 122 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 84 122 2 5 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 84 122 (Polychromatic418967fa.accept_20_9_4_2_1_1900 9 84 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 122 2 4 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 122 (accept_3_2 7 84 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 122 2 3 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 84 122 (Polychromatic418967fa.accept_20_5_4_2_1_5912 5 84 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 122 2 2 42 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 122
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 84 122 2 1 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 122 (accept_3_2 1 84 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  122))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 83 122 (Eq.refl Bool.true) (allA_succ_of_accept 39 83 122
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 83 122 (Polychromatic418967fa.accept_11_5_6_1_1_988 38 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 122 (accept_3_2 37 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 83 122 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 122 (Polychromatic418967fa.accept_9_8_2_5_1_237 35
  83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 122 (accept_3_2 34 83
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 122 (Polychromatic418967fa.accept_4_1_3_2_1_3
  33 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 122
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 122 (accept_3_2 31 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 122 (accept_3_2 28 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 122
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 122 (accept_3_2 25 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 122 (accept_3_2 22 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 122
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 122 (accept_3_2 19 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 122 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 122 (accept_3_2 16 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 122
  (Polychromatic418967fa.accept_17_14_15_3_1_4618 14 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 122 (accept_3_2 13 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 122 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 122 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 122 (accept_3_2 10 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 122
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 122 (accept_3_2 7 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  122 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 122 (accept_3_2 4 83 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 83 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  83 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 122 (accept_3_2 1 83 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83 122)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 82
  122 (Eq.refl Bool.true) (allA_of_3_0 41 82 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 81 122 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 81 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 122 (accept_3_2 40 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 122
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 122 (accept_3_2 37 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 122 (accept_3_2 34 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 122 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 81 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 122
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 32 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 122 (accept_3_2 31 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 122 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 122 (accept_3_2 28 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 122
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 122 (accept_3_2 25 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 122 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 122 (accept_3_2 22 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 122 (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 81 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 122
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 122 (accept_3_2 19 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 122 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 122 (accept_3_2 16 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 122
  (Polychromatic418967fa.accept_13_1_3_5_1_140 14 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 122 (accept_3_2 13 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 122 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 122 (accept_3_2 10 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 122 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 81 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 122
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 122 (accept_3_2 7 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  122 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 122 (accept_3_2 4 81 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 122 (Polychromatic418967fa.accept_13_2_3_5_1_2294 2
  81 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 122 (accept_3_2 1 81 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 122)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 80
  122 (Eq.refl Bool.true) (allA_succ_of_gcd 42 80 122 2 21 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 122 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 80 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 122 2 20 40 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 122
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 80 122 2 19 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 80 122 (accept_3_2 37 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80
  122 2 18 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  80 122 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 80 122 2 17 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 80 122 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 80 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 122 2 16 40 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 122 (accept_3_2 31 80 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 122 2 15 40 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 122
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 80 122 2 14 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 80 122 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 80 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 122 2 13 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 122 (accept_3_2 25 80 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 122 2 12 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 122 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 80 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 122 2 11 40 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 122
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 122 2 10 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 122 (accept_3_2 19 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  122 2 9 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 122 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 122 2 8 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 122 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 80 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 122 2 7 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 122 (accept_3_2 13 80 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 122 2 6 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 80 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 122 2 5 40 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 122
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 122 2 4 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 122 (accept_3_2 7 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 122
  2 3 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  122 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 80 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 80 122 2 2 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 80 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 80 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 122 2 1 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 122 (accept_3_2 1 80 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 122))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 79 122 (Eq.refl Bool.true)
  (allA_of_3_0 44 79 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 78 122 (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 78 122 2 22 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 78 122 (accept_3_2 43 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78
  122 2 21 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  78 122 (Polychromatic418967fa.accept_17_7_10_3_1_1421 41 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 78 122 2 20 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 78 122 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 78 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 122 2 19 39 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 122 (accept_3_2 37 78 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 122 2 18 39 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 122
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 122 2 17 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 78 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 78 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 122 2 16 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 122 (accept_3_2 31 78 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 122 2 15 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 122 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 122 2 14 39 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 122
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 122 2 13 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 122 (accept_3_2 25 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78
  122 2 12 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  78 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 78 122 2 11 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 78 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 122 2 10 39 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 122 (accept_3_2 19 78 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 122 2 9 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 122 (Polychromatic418967fa.accept_9_8_6_5_1_513 17
  78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 122 2 8 39 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 122
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 78 122 2 7 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 78 122 (accept_3_2 13 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78
  122 2 6 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  78 122 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 78 122 2 5 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 78 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 78 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 122 2 4 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 122 (accept_3_2 7 78 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 122 2 3 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 78 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 78 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 122 2 2 39 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 122
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 122 2 1 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 122 (accept_3_2 1 78 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  122))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 77 122 (Eq.refl Bool.true) (allA_succ_of_accept 45 77
  122 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 77 122 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 77 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 122 (accept_3_2 43 77 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 77 122 (Polychromatic418967fa.accept_23_19_8_7_1_2745 42 77 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 122
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 122 (accept_3_2 40 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 122 (Polychromatic418967fa.accept_20_18_17_2_1_5941 38 77 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 122 (accept_3_2 37 77 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 122 (Polychromatic418967fa.accept_21_15_14_17_1_5940 36 77
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 122 (accept_3_2 34 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 122 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 122 (accept_3_2 31 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 122 (Polychromatic418967fa.accept_13_4_12_5_1_476 30 77 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 122
  (Polychromatic418967fa.accept_10_9_7_2_1_887 29 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 122 (accept_3_2 28 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 122 (Polychromatic418967fa.accept_18_8_5_14_1_3353 26 77 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 122 (accept_3_2 25 77 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 122 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 77 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 122 (accept_3_2 22 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 122 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 122 (accept_3_2 19 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 122 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 77 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 122
  (Polychromatic418967fa.accept_13_4_12_5_1_476 17 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 122 (accept_3_2 16 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 122 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 122 (accept_3_2 13 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 122 (Polychromatic418967fa.accept_16_12_13_10_1_2637 12 77 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 122 (accept_3_2 10 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 122 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 122 (accept_3_2 7 77 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 122 (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 77 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 122
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 122 (accept_3_2 4 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 122 (Polychromatic418967fa.accept_13_2_12_5_1_1602 2 77 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 122 (accept_3_2 1 77 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 122)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 76 122 (Eq.refl Bool.true)
  (allA_of_3_0 47 76 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 75 122 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 122 (accept_3_2 46 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 44
  75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 122 (accept_3_2 43 75
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 122
  (Polychromatic418967fa.accept_9_6_3_5_1_240 42 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 122 (accept_3_2 40 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 122 (Polychromatic418967fa.accept_19_1_18_8_1_1066 39 75 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 122
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 122 (accept_3_2 37 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 122 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 122 (accept_3_2 34 75 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 122
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 122 (accept_3_2 31 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 122 (accept_3_2 28 75 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 122 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 75 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 122
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 122 (accept_3_2 25 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 122 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 122 (accept_3_2 22 75 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 122
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 122 (accept_3_2 19 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 122 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 122 (accept_3_2 16 75 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 122 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 75 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 122
  (Polychromatic418967fa.accept_33_14_9_23_1_5939 14 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 122 (accept_3_2 13 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 122 (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 122 (accept_3_2 10 75 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 122
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 122 (accept_3_2 7 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  122 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 75 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 122 (accept_3_2 4 75 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 122 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 75 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 75
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 122 (accept_3_2 1 75 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 122)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  49 74 122 (Eq.refl Bool.true) (allA_succ_of_gcd 48 74 122 2 24 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 122 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 74 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 122 2 23 37 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 122
  (Polychromatic418967fa.accept_22_1_8_12_1_5938 45 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 122 2 22 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 74 122 (accept_3_2 43 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74
  122 2 21 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  74 122 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 74 122 2 20 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 74 122 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 74 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 122 2 19 37 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 122 (accept_3_2 37 74 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 122 2 18 37 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 122
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 74 122 2 17 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 74 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 74 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 122 2 16 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 122 (accept_3_2 31 74 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 122 2 15 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 74 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 122 2 14 37 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 122
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 122 2 13 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 74 122 (accept_3_2 25 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74
  122 2 12 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  74 122 (Polychromatic418967fa.accept_19_4_17_8_1_2103 23 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 74 122 2 11 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 74 122 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 74 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 122 2 10 37 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 122 (accept_3_2 19 74 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 122 2 9 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 74 122 (Polychromatic418967fa.accept_9_8_2_5_1_237 17
  74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 122 2 8 37 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 122
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 122 2 7 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 122 (accept_3_2 13 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  122 2 6 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 122 (Polychromatic418967fa.accept_18_11_2_14_1_3351 11 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 122 2 5 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 122 (Polychromatic418967fa.accept_17_9_6_3_1_2398 9 74 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 122 2 4 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 122 (accept_3_2 7 74 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 122 2 3 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 122 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 74 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 122 2 2 37 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 122
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 122 2 1 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 122 (accept_3_2 1 74 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  122))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 73 122 (Eq.refl Bool.true) (allA_of_3_0 50 73 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 72 122 (Eq.refl Bool.true) (allA_succ_of_gcd 50 72 122 2 25 36
  61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 122
  (accept_3_2 49 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 122 2 24 36 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 122
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 72 122 2 23 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 72 122 (Polychromatic418967fa.accept_19_7_15_8_1_1089 45 72 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 122 2 22 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 122 (accept_3_2 43 72 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 122 2 21 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 122 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 72 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 122 2 20 36 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 72 122
  (Polychromatic418967fa.accept_19_1_15_8_1_4538 39 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 72 122 2 19 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 72 122 (accept_3_2 37 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72
  122 2 18 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  72 122 (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 72 122 2 17 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 72 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 122 2 16 36 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 122 (accept_3_2 31 72 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 122 2 15 36 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 122
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 72 122 2 14 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 72 122 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 122 2 13 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 122 (accept_3_2 25 72 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 122 2 12 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 122 (Polychromatic418967fa.accept_19_4_15_8_1_5937 23 72 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 122 2 11 36 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 122
  (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 122 2 10 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 122 (accept_3_2 19 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  122 2 9 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 122 (Polychromatic418967fa.accept_19_17_15_8_1_5936 17 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 122 2 8 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 122 2 7 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 122 (accept_3_2 13 72 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 122 2 6 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 72 122 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 72 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 122 2 5 36 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 122
  (Polychromatic418967fa.accept_20_9_12_2_1_5935 9 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 122 2 4 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 122 (accept_3_2 7 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 122
  2 3 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  122 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 122 2 2 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 72 122 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 72 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 122 2 1 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 122 (accept_3_2 1 72 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 122))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 71 122 (Eq.refl
  Bool.true) (allA_succ_of_accept 51 71 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 122 (Polychromatic418967fa.accept_11_6_5_1_1_586
  50 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 122 (accept_3_2 49
  71 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 122
  (Polychromatic418967fa.accept_9_3_8_5_1_65 48 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 71 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 122 (accept_3_2 46 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 71 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 122 (accept_3_2 43 71
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 122
  (Polychromatic418967fa.accept_9_6_8_5_1_837 42 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 71 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 122 (accept_3_2 40 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 71 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 38
  71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 122 (accept_3_2 37 71
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 122
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 71 122 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 122 (accept_3_2 34 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 71 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 122 (Polychromatic418967fa.accept_7_4_1_3_1_277 32
  71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 122 (accept_3_2 31 71
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 122
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 71 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 122 (accept_3_2 28 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 71 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 26
  71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 122 (accept_3_2 25 71
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 122
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 71 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 122 (accept_3_2 22 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 71 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 20
  71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 122 (accept_3_2 19 71
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 122
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 71 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 122 (accept_3_2 16 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 71 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 122 (Polychromatic418967fa.accept_13_1_6_5_1_1610
  14 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 122 (accept_3_2 13
  71 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 122
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 71 122 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 122 (accept_3_2 10 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 71 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 122 (Polychromatic418967fa.accept_12_8_11_2_1_1277
  8 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 122 (accept_3_2 7 71
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 122 (Polychromatic418967fa.accept_9_6_8_5_1_837
  6 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 122
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 122 (accept_3_2 4 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  122 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 122 (accept_3_2 1 71 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 122)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 70 122 (Eq.refl
  Bool.true) (allA_of_3_0 53 70 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 69 122 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 69 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 122 (accept_3_2 52 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 69 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 122
  (Polychromatic418967fa.accept_27_23_15_14_1_5934 50 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 69 122 (accept_3_2 49 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 69 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 122 (accept_3_2 46 69 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 122 (Polychromatic418967fa.accept_13_6_4_5_1_2330
  45 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 122
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 122 (accept_3_2 43 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 122 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 122 (accept_3_2 40 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 122
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 122 (accept_3_2 37 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 122 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 122 (accept_3_2 34 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 122 (Polychromatic418967fa.accept_20_13_9_2_1_5933 33 69 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 122
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 122 (accept_3_2 31 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 122 (accept_3_2 28 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 122
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 122 (accept_3_2 25 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 122 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 122 (accept_3_2 22 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 122
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 122 (accept_3_2 19 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 122 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 122 (accept_3_2 16 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 122
  (Polychromatic418967fa.accept_13_1_4_5_1_113 14 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 122 (accept_3_2 13 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 122 (accept_3_2 10 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 122
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 122 (accept_3_2 7 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  122 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 122 (accept_3_2 4 69 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  69 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 122 (accept_3_2 1 69 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69 122))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 68 122 (Eq.refl Bool.true) (allA_succ_of_gcd 54 68 122 2 27 34 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 68 122
  (Polychromatic418967fa.accept_12_5_8_2_1_309 53 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 68 122 2 26 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 68 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 68 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 122 2 25 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 122 (accept_3_2 49 68 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 122 2 24 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 122 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 68 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 122 2 23 34 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 122
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 68 122 2 22 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 68 122 (accept_3_2 43 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68
  122 2 21 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  68 122 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 68 122 2 20 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 68 122 (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 68 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 122 2 19 34 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 122 (accept_3_2 37 68 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 122 2 18 34 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 68 122
  (Polychromatic418967fa.accept_10_5_8_2_1_517 35 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 68 122 2 17 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 68 122 (Polychromatic418967fa.accept_14_5_12_10_1_2985 33 68 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 122 2 16 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 122 (accept_3_2 31 68 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 122 2 15 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 122 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 68 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 122 2 14 34 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 122
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 122 2 13 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 68 122 (accept_3_2 25 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68
  122 2 12 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  68 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 68 122 2 11 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 68 122 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 68 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 122 2 10 34 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 122 (accept_3_2 19 68 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 122 2 9 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 68 122 (Polychromatic418967fa.accept_12_5_8_2_1_309 17
  68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 122 2 8 34 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 122
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 122 2 7 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 122 (accept_3_2 13 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  122 2 6 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 122 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 122 2 5 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 68 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 122 2 4 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 122 (accept_3_2 7 68 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 122 2 3 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 122 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 68 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 122 2 2 34 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 122
  (Polychromatic418967fa.accept_11_3_2_1_1_994 3 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 122 2 1 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 122 (accept_3_2 1 68 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  122))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 67 122 (Eq.refl Bool.true) (allA_of_3_0 56
  67 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 66 122 (Eq.refl Bool.true) (allA_succ_of_gcd 56 66 122
  2 28 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66
  122 (accept_3_2 55 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 122 2 27 33 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 122
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 66 122 2 26 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 66 122 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 66 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 122 2 25 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 122 (accept_3_2 49 66 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 122 2 24 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 122 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 66 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 122 2 23 33 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 122
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 122 2 22 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 122 (accept_3_2 43 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66
  122 2 21 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  66 122 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 66 122 2 20 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 66 122 (Polychromatic418967fa.accept_12_3_6_2_1_747 39 66 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 122 2 19 33 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 122 (accept_3_2 37 66 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 122 2 18 33 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 122
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 66 122 2 17 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 66 122 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 66 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 122 2 16 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 122 (accept_3_2 31 66 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 122 2 15 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 122 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 66 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 122 2 14 33 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 122
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 122 2 13 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 122 (accept_3_2 25 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66
  122 2 12 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  66 122 (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 66 122 2 11 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 66 122 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 66 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 122 2 10 33 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 122 (accept_3_2 19 66 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 122 2 9 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 122 (Polychromatic418967fa.accept_9_8_3_5_1_241 17
  66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 122 2 8 33 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 122
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 66 122 2 7 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 66 122 (accept_3_2 13 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66
  122 2 6 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  66 122 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 66 122 2 5 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 66 122 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 66 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 122 2 4 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 122 (accept_3_2 7 66 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 122 2 3 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 66 122 (Polychromatic418967fa.accept_41_5_25_40_1_5932 5 66 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 122 2 2 33 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 122
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 66 122 2 1 33 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 122 (accept_3_2 1 66 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  122))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 65 122 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 65 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 122 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 65 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 122 (accept_3_2 55 65 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 54
  65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 122
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 122 (accept_3_2 52 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 122 (accept_3_2 49 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 122 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 65 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 122 (accept_3_2 46 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 122 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 122 (accept_3_2 43 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 122
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 122 (accept_3_2 40 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 122 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 122 (accept_3_2 37 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 65 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 122 (accept_3_2 34 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 122 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 122 (accept_3_2 31 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 122 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 65 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 122
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 122 (accept_3_2 28 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 122 (accept_3_2 25 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 65 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 122 (accept_3_2 22 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 122 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 122 (accept_3_2 19 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 122 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 65 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 122
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 122 (accept_3_2 16 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 122 (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 65 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 122 (accept_3_2 13 65 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 65 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 122 (accept_3_2 10 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 122 (accept_3_2 7 65 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 122 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 65 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 122
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 122 (accept_3_2 4 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 122 (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 122 (accept_3_2 1 65 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 122)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 64 122 (Eq.refl
  Bool.true) (allA_of_3_0 59 64 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 63 122 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 63 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 122 (accept_3_2 58 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 63 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 122
  (Polychromatic418967fa.accept_23_10_17_7_1_5931 56 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 122 (accept_3_2 55 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 122 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 122 (accept_3_2 52 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 122 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 63 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 122
  (Polychromatic418967fa.accept_15_5_3_2_1_5930 50 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 122 (accept_3_2 49 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 122 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 122 (accept_3_2 46 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 122
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 44 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 122 (accept_3_2 43 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 122 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 122 (accept_3_2 40 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 122 (Polychromatic418967fa.accept_14_11_7_10_1_4852 39 63 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 122
  (Polychromatic418967fa.accept_20_18_3_2_1_5929 38 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 122 (accept_3_2 37 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 122 (Polychromatic418967fa.accept_19_17_6_8_1_5928 36 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 122 (accept_3_2 34 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 122
  (Polychromatic418967fa.accept_13_6_11_5_1_133 32 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 122 (accept_3_2 31 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 122 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 122 (accept_3_2 28 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 122 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 63 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 122
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 122 (accept_3_2 25 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 122 (Polychromatic418967fa.accept_17_7_12_3_1_4693 24 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 122 (accept_3_2 22 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 122
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 20 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 122 (accept_3_2 19 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 122 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 122 (accept_3_2 16 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 122 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 63 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 122
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 122 (accept_3_2 13 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 122 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 122 (accept_3_2 10 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 122
  (Polychromatic418967fa.accept_17_8_12_3_1_5927 8 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 122 (accept_3_2 7 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  122 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 122 (accept_3_2 4 63 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 122 (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 63 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 122 (Polychromatic418967fa.accept_19_2_6_8_1_3284 2
  63 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 122 (accept_3_2 1 63 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 122))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 62 122 (Eq.refl Bool.true) (allA_succ_of_gcd 60 62 122 2 30 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 122
  (Polychromatic418967fa.accept_14_3_6_10_1_752 59 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 122 2 29 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 62 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 122 2 28 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 122 (accept_3_2 55 62 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 122 2 27 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 122 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 62 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 122 2 26 31 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 122
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 122 2 25 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 122 (accept_3_2 49 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  122 2 24 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 122 2 23 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 122 (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 62 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 122 2 22 31 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 122 (accept_3_2 43 62 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 122 2 21 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 122
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 41 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 122 2 20 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 122 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 62 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 122 2 19 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 122 (accept_3_2 37 62 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 122 2 18 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 122 (Polychromatic418967fa.accept_19_16_5_8_1_3253 35 62 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 122 2 17 31 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 122
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 122 2 16 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 122 (accept_3_2 31 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  122 2 15 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 122 2 14 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 122 (Polychromatic418967fa.accept_17_10_11_3_1_3442 27 62 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 122 2 13 31 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 122 (accept_3_2 25 62 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 122 2 12 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 122
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 122 2 11 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 62 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 122 2 10 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 122 (accept_3_2 19 62 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 122 2 9 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 122 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 62 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 122 2 8 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 122
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 122 2 7 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 122 (accept_3_2 13 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  122 2 6 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 122 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 122 2 5 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 62 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 122 2 4 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 122 (accept_3_2 7 62 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 122 2 3 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 122 (Polychromatic418967fa.accept_16_5_14_10_1_3644 5 62 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 122 2 2 31 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 122
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 122 2 1 31 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 122 (accept_3_2 1 62 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  122))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 122 (allA_of_3_0 61 61 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 122 (allA_succ_of_accept 59 60 122
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 59 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 60 122 2 29 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 60 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 60 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 122 2 28 30 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 122 (accept_3_2 55 60 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 122 2 27 30 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 122
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 60 122 2 26 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 60 122 (Polychromatic418967fa.accept_13_12_8_5_1_976 51 60 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 122 2 25 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 122 (accept_3_2 49 60 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 122 2 24 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 122 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 60 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 122 2 23 30 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 122
  (Polychromatic418967fa.accept_16_13_12_10_1_3540 45 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 60 122 2 22 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 60 122 (accept_3_2 43 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 122 2 21 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 122 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 60 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 122 2 20 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 39
  60 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 122 2 19 30 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 122 (accept_3_2 37
  60 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 122 2 18 30 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 122
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 60 122 2 17 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 60 122 (Polychromatic418967fa.accept_19_14_3_8_1_5920 33 60 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 122 2 16 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 122 (accept_3_2 31 60 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 122 2 15 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 60 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 122 2 14 30 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 122
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 60 122 2 13 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 60 122 (accept_3_2 25 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60
  122 2 12 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  60 122 (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 60 122 2 11 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 60 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 122 2 10 30 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 122 (accept_3_2 19 60 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 122 2 9 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 122 (Polychromatic418967fa.accept_9_8_6_5_1_513 17
  60 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 122 2 8 30 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 122
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 60 122 2 7 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 60 122 (accept_3_2 13 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60
  122 2 6 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  60 122 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 60 122 2 5 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 60 122 (Polychromatic418967fa.accept_18_9_6_14_1_5913 9 60 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 122 2 4 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 122 (accept_3_2 7 60 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 122 2 3 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 60 122 (Polychromatic418967fa.accept_16_5_12_10_1_3508 5 60 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 122 2 2 30 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 122
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 122 2 1 30 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 122 (accept_3_2 1 60 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  122)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 122 (allA_succ_of_accept 58 59 122
  (accept_3_2 58 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 122
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 122 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 59 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 122 (accept_3_2 55 59 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 122 (Polychromatic418967fa.accept_13_2_7_5_1_3189 54 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 53
  59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 122 (accept_3_2 52 59
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 122 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 122
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 50 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 122 (accept_3_2 49 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 122 (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 122 (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 122 (accept_3_2 46 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 122
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 122 (accept_3_2 43 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 122 (Polychromatic418967fa.accept_15_12_14_2_1_3794 42 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 122 (accept_3_2 40 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 122
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 38 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 122 (accept_3_2 37 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 122 (Polychromatic418967fa.accept_22_14_15_12_1_2866 36 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 122 (Polychromatic418967fa.accept_14_7_3_10_1_1364 35 59 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 122 (accept_3_2 34 59 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 122
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 122 (accept_3_2 31 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 122 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 122 (accept_3_2 28 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 122
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 26 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 122 (accept_3_2 25 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 122 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 122 (Polychromatic418967fa.accept_20_3_19_2_1_5926 23 59 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 122 (accept_3_2 22 59 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 122
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 122 (accept_3_2 19 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 122 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 122 (accept_3_2 16 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 122
  (Polychromatic418967fa.accept_19_14_2_8_1_5925 14 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 122 (accept_3_2 13 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 122 (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 122 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 122 (accept_3_2 10 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 122
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 122 (accept_3_2 7 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  122 (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 59 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 122 (accept_3_2 4 59 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 122
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 2 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 122 (accept_3_2 1 59 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  122))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 122 (allA_of_3_0 58 58 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 57 122 (allA_succ_of_accept 56 57 122
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 122 (accept_3_2 55 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 122 (accept_3_2 52 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 57 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 122
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 50 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 122 (accept_3_2 49 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 122 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 122 (accept_3_2 46 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 122 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 57 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 122
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 122 (accept_3_2 43 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 122 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 122 (accept_3_2 40 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 122
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 122 (accept_3_2 37 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 122 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 122 (accept_3_2 34 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 57 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 122
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 122 (accept_3_2 31 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 122 (accept_3_2 28 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 122
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 122 (accept_3_2 25 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 122 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 122 (accept_3_2 22 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 122 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 57 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 122
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 122 (accept_3_2 19 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 122 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 122 (accept_3_2 16 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 122
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 122 (accept_3_2 13 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 122 (accept_3_2 10 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 57 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 122
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 122 (accept_3_2 7 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  122 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 122 (accept_3_2 4 57 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  57 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 122 (accept_3_2 1 57 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 122)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 122 (allA_succ_of_accept 55 56 122 (accept_3_2 55 56 122 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 122 2 27 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 122 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 122 2 26 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 51
  56 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 122 2 25 28 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 122 (accept_3_2 49
  56 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 122 2 24 28 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 122
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 56 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 122 2 23 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 122 (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 56 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 122 2 22 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 122 (accept_3_2 43 56 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 122 2 21 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 122 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 56 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 122 2 20 28 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 122
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 56 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 122 2 19 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 122 (accept_3_2 37 56 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  122 2 18 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 122 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 122 2 17 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 56 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 122 2 16 28 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 122 (accept_3_2 31 56 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 122 2 15 28 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 122
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 56 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 122 2 14 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 122 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 56 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 122 2 13 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 122 (accept_3_2 25 56 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 122 2 12 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 122 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 56 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 122 2 11 28 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 122
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 56 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 122 2 10 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 122 (accept_3_2 19 56 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  122 2 9 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 122 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 122 2 8 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 56 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 122 2 7 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 122 (accept_3_2 13 56 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 122 2 6 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 56 122 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 56 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 122 2 5 28 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 122
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 56 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 122 2 4 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 122 (accept_3_2 7 56 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 122
  2 3 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  122 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 56 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 122 2 2 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 122 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 56 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 122 2 1 28 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 122 (accept_3_2 1 56 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 122)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 122 (allA_of_3_0 55
  55 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 122 (allA_succ_of_accept 53 54 122
  (Polychromatic418967fa.accept_11_9_10_1_1_581 53 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 122 2 26 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 54 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 122 2 25 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 122 (accept_3_2 49 54 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 122 2 24 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 122 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 54 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 122 2 23 27 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 122
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 122 2 22 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 122 (accept_3_2 43 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54
  122 2 21 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  54 122 (Polychromatic418967fa.accept_15_11_9_2_1_4780 41 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 122 2 20 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 122 (Polychromatic418967fa.accept_12_3_6_2_1_747 39 54 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 122 2 19 27 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 122 (accept_3_2 37 54 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 122 2 18 27 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 122
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 122 2 17 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 54 122 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 54 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 122 2 16 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 122 (accept_3_2 31 54 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 122 2 15 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 122 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 54 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 122 2 14 27 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 122
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 122 2 13 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 122 (accept_3_2 25 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54
  122 2 12 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  54 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 54 122 2 11 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 54 122 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 54 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 122 2 10 27 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 122 (accept_3_2 19 54 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 122 2 9 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 122 (Polychromatic418967fa.accept_10_7_4_2_1_903 17
  54 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 122 2 8 27 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 122
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 122 2 7 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 122 (accept_3_2 13 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54
  122 2 6 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  54 122 (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 122 2 5 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 54 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 122 2 4 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 122 (accept_3_2 7 54 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 122 2 3 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 54 122 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 54 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 122 2 2 27 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 122
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 122 2 1 27 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 122 (accept_3_2 1 54 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  122)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 122 (allA_succ_of_accept 52 53 122 (accept_3_2
  52 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 53 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 122 (accept_3_2 49 53 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 122 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 122 (accept_3_2 46 53
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 122 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 122
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 53 122 (accept_3_2 43 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  53 122 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 53 122 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 122 (accept_3_2 40 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 122
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 122 (accept_3_2 37 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 122 (accept_3_2 34 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 122
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 122 (accept_3_2 31 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 122 (accept_3_2 28 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 122
  (Polychromatic418967fa.accept_19_7_15_8_1_1089 26 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 122 (accept_3_2 25 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 122 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 122 (accept_3_2 22 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 122
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 122 (accept_3_2 19 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 122 (Polychromatic418967fa.accept_17_1_2_3_1_4668 18 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 122 (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 122 (accept_3_2 16 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 122
  (Polychromatic418967fa.accept_16_14_5_10_1_3622 14 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 122 (accept_3_2 13 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 122 (accept_3_2 10 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 122
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 122 (accept_3_2 7 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  122 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 122 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 53 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 122 (accept_3_2 4 53 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  53 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 122 (accept_3_2 1 53 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 122)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 122 (allA_of_3_0 52 52 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 122
  (allA_succ_of_accept 50 51 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 51 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 122 (accept_3_2 49 51 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 122 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 122 (accept_3_2 46 51
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 122 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 122
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 122 (accept_3_2 43 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 122 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 122 (accept_3_2 40 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 51 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 122
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 122 (accept_3_2 37 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 122 (accept_3_2 34 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 122
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 32 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 122 (accept_3_2 31 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 122 (accept_3_2 28 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 122 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 51 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 122
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 122 (accept_3_2 25 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 122 (Polychromatic418967fa.accept_19_5_13_8_1_3229 24 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 122 (accept_3_2 22 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 122
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 122 (accept_3_2 19 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 122 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 122 (accept_3_2 16 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 122
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 14 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 122 (accept_3_2 13 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 122 (accept_3_2 10 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 122
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 122 (accept_3_2 7 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  122 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 122 (accept_3_2 4 51 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 51 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 122 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  51 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 122 (accept_3_2 1 51 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 122)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 122 (allA_succ_of_accept 49 50 122 (accept_3_2 49 50 122 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 122 2 24 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 50 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 50 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 122 2 23 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 122 (Polychromatic418967fa.accept_13_6_11_5_1_133
  45 50 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 122 2 22 25 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 122 (accept_3_2 43
  50 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 122 2 21 25 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 122
  (Polychromatic418967fa.accept_15_11_5_2_1_520 41 50 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 122 2 20 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 122 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 50 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 122 2 19 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 122 (accept_3_2 37 50 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 122 2 18 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 122 (Polychromatic418967fa.accept_20_15_10_2_1_5924 35 50
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 122 2 17 25 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 122
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 50 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 122 2 16 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 50 122 (accept_3_2 31 50 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50
  122 2 15 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  50 122 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 50 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 122 2 14 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 122 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 50 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 122 2 13 25 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 122 (accept_3_2 25 50 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 122 2 12 25 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 122
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 50 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 122 2 11 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 122 (Polychromatic418967fa.accept_17_4_16_3_1_4620 21 50 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 122 2 10 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 122 (accept_3_2 19 50 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 122 2 9 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 122 (Polychromatic418967fa.accept_22_17_6_12_1_5923 17 50 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 122 2 8 25 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 122
  (Polychromatic418967fa.accept_19_15_12_8_1_5922 15 50 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 122 2 7 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 122 (accept_3_2 13 50 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  122 2 6 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 122 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 50 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 122 2 5 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 50 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 122 2 4 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 122 (accept_3_2 7 50 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 122 2 3 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 50 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 122 2 2 25 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 122
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 50 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 122 2 1 25 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 122 (accept_3_2 1 50 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  122)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 122 (allA_of_3_0 49 49 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 122 (allA_succ_of_accept 47 48 122 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 48
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 122 2 23 24 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 122
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 48 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 122 2 22 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 122 (accept_3_2 43 48 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48
  122 2 21 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  48 122 (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 48 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 48 122 2 20 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 48 122 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 122 2 19 24 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 122 (accept_3_2 37 48 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 122 2 18 24 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 122
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 122 2 17 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 48 122 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 122 2 16 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 122 (accept_3_2 31 48 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 122 2 15 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 122 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 48 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 122 2 14 24 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 122
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 48 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 122 2 13 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 122 (accept_3_2 25 48 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48
  122 2 12 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  48 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 48 122 2 11 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 48 122 (Polychromatic418967fa.accept_18_3_12_14_1_2232 21 48 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 122 2 10 24 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 122 (accept_3_2 19 48 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 122 2 9 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 122 (Polychromatic418967fa.accept_9_8_3_5_1_241 17
  48 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 122 2 8 24 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 122
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 48 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 48 122 2 7 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 122 (accept_3_2 13 48 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48
  122 2 6 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  48 122 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 48 122 2 5 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 48 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 122 2 4 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 122 (accept_3_2 7 48 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 122 2 3 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 48 122 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 48 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 122 2 2 24 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 122
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 48 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 48 122 2 1 24 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 122 (accept_3_2 1 48 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  122)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 122 (allA_succ_of_accept 46 47 122 (accept_3_2 46 47
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 122 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 122
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 122 (accept_3_2 43 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 122 (accept_3_2 40 47 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 122
  (Polychromatic418967fa.accept_13_12_8_5_1_976 38 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 122 (accept_3_2 37 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 122 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 122 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 122 (accept_3_2 34 47 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 122
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 122 (accept_3_2 31 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 122 (accept_3_2 28 47 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 122
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 122 (accept_3_2 25 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 47 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 122 (accept_3_2 22 47 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 122
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 122 (accept_3_2 19 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 122 (Polychromatic418967fa.accept_19_18_9_8_1_3267 18 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 122 (accept_3_2 16 47 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 122
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 122 (accept_3_2 13 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 122 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 122 (Polychromatic418967fa.accept_16_11_15_10_1_3515 11 47 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 122 (accept_3_2 10 47 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 122
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 122 (accept_3_2 7 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  122 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 47 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 122 (accept_3_2 4 47 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 47
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 122 (accept_3_2 1 47 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 122))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  122 (allA_of_3_0 46 46 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 122 (allA_succ_of_accept 44 45 122
  (Polychromatic418967fa.accept_16_12_13_10_1_2637 44 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 45 122 (accept_3_2 43 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 122 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 45 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 122 (accept_3_2 40 45 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 122
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 122 (accept_3_2 37 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 122 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 122 (accept_3_2 34 45 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 122 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 45 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 122
  (Polychromatic418967fa.accept_27_5_18_14_1_5921 32 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 122 (accept_3_2 31 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 122 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 122 (accept_3_2 28 45 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 122
  (Polychromatic418967fa.accept_17_9_11_3_1_2353 26 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 122 (accept_3_2 25 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 122 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 122 (accept_3_2 22 45 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 122 (Polychromatic418967fa.accept_14_7_3_10_1_1364 21 45 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 122
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 20 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 122 (accept_3_2 19 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 122 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 122 (accept_3_2 16 45 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 122
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 122 (accept_3_2 13 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 122 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 122 (accept_3_2 10 45 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 122 (Polychromatic418967fa.accept_17_9_11_3_1_2353 9 45 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 122
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 122 (accept_3_2 7 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  122 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 122 (accept_3_2 4 45 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 122 (Polychromatic418967fa.accept_17_2_11_3_1_4654
  2 45 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 122 (accept_3_2 1 45
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 122))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  44 122 (allA_succ_of_accept 43 44 122 (accept_3_2 43 44 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  42 44 122 2 21 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 44 122 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 44 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 122 2 20 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 39
  44 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 122 2 19 22 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 122 (accept_3_2 37
  44 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 122 2 18 22 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 122
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 44 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 122 2 17 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 44 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 44 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 122 2 16 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 122 (accept_3_2 31 44 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 122 2 15 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 44 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 122 2 14 22 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 122
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 44 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 122 2 13 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 44 122 (accept_3_2 25 44 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44
  122 2 12 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  44 122 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 44 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 44 122 2 11 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 44 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 44 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 122 2 10 22 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 122 (accept_3_2 19 44 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 122 2 9 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 122 (Polychromatic418967fa.accept_10_7_4_2_1_903 17
  44 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 122 2 8 22 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 122
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 44 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 122 2 7 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 122 (accept_3_2 13 44 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44
  122 2 6 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  44 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 44 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 122 2 5 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 122 (Polychromatic418967fa.accept_17_9_10_3_1_3423 9 44 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 122 2 4 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 122 (accept_3_2 7 44 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 122 2 3 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 44 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 44 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 122 2 2 22 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 122
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 44 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 122 2 1 22 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 122 (accept_3_2 1 44 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  122)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 122 (allA_of_3_0 43 43 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 42 122 (allA_succ_of_accept 41 42 122 (Polychromatic418967fa.accept_13_2_3_5_1_2294 41 42 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 122 2 20 21 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 122
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 122 2 19 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 122 (accept_3_2 37 42 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42
  122 2 18 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  42 122 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 42 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 42 122 2 17 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 42 122 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 42 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 122 2 16 21 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 122 (accept_3_2 31 42 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 122 2 15 21 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 122
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 122 2 14 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 42 122 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 42 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 122 2 13 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 122 (accept_3_2 25 42 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 122 2 12 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 122 (Polychromatic418967fa.accept_22_1_20_12_1_2869 23 42
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 122 2 11 21 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 122
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 122 2 10 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 122 (accept_3_2 19 42 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42
  122 2 9 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  42 122 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 122 2 8 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 122 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 42 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 122 2 7 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 122 (accept_3_2 13 42 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 122 2 6 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 42 122 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 122 2 5 21 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 122
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 42 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 122 2 4 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 122 (accept_3_2 7 42 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 122
  2 3 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42
  122 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 42 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 122 2 2 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 122 2 1 21 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 122 (accept_3_2 1 42 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 42 122)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 122 (allA_succ_of_accept
  40 41 122 (accept_3_2 40 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 122
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 122 (Polychromatic418967fa.accept_13_12_2_5_1_1634 38 41 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 122 (accept_3_2 37 41 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 122 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 41 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 122 (accept_3_2 34 41
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 122 (Polychromatic418967fa.accept_6_3_5_2_1_12
  33 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 122
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 122 (accept_3_2 31 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 122 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 41 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 122 (accept_3_2 28 41 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 122
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 122 (accept_3_2 25 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 122 (Polychromatic418967fa.accept_15_9_11_2_1_1882 24 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 122 (accept_3_2 22 41 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 122
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 122 (accept_3_2 19 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 122 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 122 (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 41 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 122 (accept_3_2 16 41 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 122
  (Polychromatic418967fa.accept_19_14_3_8_1_5920 14 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 122 (accept_3_2 13 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 122 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 122 (accept_3_2 10 41 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 122
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 122 (accept_3_2 7 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  122 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 122 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 41 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 122 (accept_3_2 4 41 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  41 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 122 (accept_3_2 1 41 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 122))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 122
  (allA_of_3_0 40 40 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 122 (allA_succ_of_accept 38 39 122
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 122 (accept_3_2 37 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 122 (accept_3_2 34 39 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 122
  (Polychromatic418967fa.accept_19_13_1_8_1_3281 32 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 122 (accept_3_2 31 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 122 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 122 (accept_3_2 28 39 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 122 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 122
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 122 (accept_3_2 25 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 122 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 122 (accept_3_2 22 39 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 122
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 122 (accept_3_2 19 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 122 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 122 (accept_3_2 16 39 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 122
  (Polychromatic418967fa.accept_16_14_7_10_1_898 14 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 122 (accept_3_2 13 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 122 (Polychromatic418967fa.accept_18_12_3_14_1_5919 12 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 122 (accept_3_2 10 39 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 122
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 122 (accept_3_2 7 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  122 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 39 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 122 (accept_3_2 4 39 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 122 (Polychromatic418967fa.accept_16_3_7_10_1_3503 3 39 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 122 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 39
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 122 (accept_3_2 1 39 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 122))))))))))))))))))))))))))))))))))))))) (allB_succ 38 122
  (allA_succ_of_accept 37 38 122 (accept_3_2 37 38 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  122 2 18 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 122 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 122 2 17 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 38 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 122 2 16 19 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 122 (accept_3_2 31 38 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 122 2 15 19 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 122
  (Polychromatic418967fa.accept_18_11_2_14_1_3351 29 38 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 122 2 14 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 122 (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 38 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 122 2 13 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 122 (accept_3_2 25 38 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 122 2 12 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 122 (Polychromatic418967fa.accept_20_3_18_2_1_5918 23 38 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 122 2 11 19 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 122
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 38 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 122 2 10 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 122 (accept_3_2 19 38 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  122 2 9 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 122 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 122 2 8 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 38 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 122 2 7 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 122 (accept_3_2 13 38 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 122 2 6 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 122 (Polychromatic418967fa.accept_18_11_2_14_1_3351 11 38 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 122 2 5 19 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 122
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 38 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 122 2 4 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 122 (accept_3_2 7 38 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 122
  2 3 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  122 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 38 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 122 2 2 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 122 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 38 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 122 2 1 19 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 122 (accept_3_2 1 38 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 122)))))))))))))))))))))))))))))))))))))) (allB_succ 37 122 (allA_of_3_0 37 37 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 122 (allA_succ_of_accept 35 36 122
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 36 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 122 2 17 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 122 2 16 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 122 (accept_3_2 31 36 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 122 2 15 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 122 (Polychromatic418967fa.accept_19_10_17_8_1_5917 29 36
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 122 2 14 18 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 122
  (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 36 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 122 2 13 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 122 (accept_3_2 25 36 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36
  122 2 12 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  36 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 122 2 11 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 122 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 36 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 122 2 10 18 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 122 (accept_3_2 19 36 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 122 2 9 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 122 (Polychromatic418967fa.accept_13_4_10_5_1_1644
  17 36 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 122 2 8 18 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 122
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 15 36 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 122 2 7 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 122 (accept_3_2 13 36 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36
  122 2 6 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  36 122 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 122 2 5 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 122 2 4 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 122 (accept_3_2 7 36 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 122 2 3 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 36 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 122 2 2 18 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 122
  (Polychromatic418967fa.accept_19_3_17_8_1_5916 3 36 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 122 2 1 18 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 122 (accept_3_2 1 36 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  122)))))))))))))))))))))))))))))))))))) (allB_succ 35 122 (allA_succ_of_accept 34 35 122 (accept_3_2 34 35 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  35 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 122
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 122 (accept_3_2 31 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 122 (accept_3_2 28 35 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 122
  (Polychromatic418967fa.accept_15_11_5_2_1_520 26 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 122 (accept_3_2 25 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 122 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 122 (Polychromatic418967fa.accept_10_3_5_2_1_38 23 35 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 122 (accept_3_2 22 35 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 122
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 122 (accept_3_2 19 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 122 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 122 (accept_3_2 16 35 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 122
  (Polychromatic418967fa.accept_11_3_2_1_1_994 14 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 122 (accept_3_2 13 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 122 (accept_3_2 10 35 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 122
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 122 (accept_3_2 7 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  122 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 35 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 122 (accept_3_2 4 35 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  35 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 122 (accept_3_2 1 35 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 122))))))))))))))))))))))))))))))))))) (allB_succ 34 122
  (allA_of_3_0 34 34 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 122 (allA_succ_of_accept 32 33 122
  (Polychromatic418967fa.accept_19_13_14_8_1_4490 32 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 122 (accept_3_2 31 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 122 (accept_3_2 28 33 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 122
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 122 (accept_3_2 25 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 122 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 122 (accept_3_2 22 33 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 122
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 122 (accept_3_2 19 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 122 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 122 (accept_3_2 16 33 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 122
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 122 (accept_3_2 13 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 122 (accept_3_2 10 33 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 122
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 122 (accept_3_2 7 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  122 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 33 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 122 (accept_3_2 4 33 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 33
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 122 (accept_3_2 1 33 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 122))))))))))))))))))))))))))))))))) (allB_succ 32 122
  (allA_succ_of_accept 31 32 122 (accept_3_2 31 32 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  122 2 15 16 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  32 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 32 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 122 2 14 16 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 32 122 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 32 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 122 2 13 16 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 122 (accept_3_2 25 32 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 122 2 12 16 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 122
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 32 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 32 122 2 11 16 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 32 122 (Polychromatic418967fa.accept_14_7_4_10_1_1351 21 32 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 122 2 10 16 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 122 (accept_3_2 19 32 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 122 2 9 16 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 32 122 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 32 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 122 2 8 16 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 122
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 32 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 32 122 2 7 16 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 32 122 (accept_3_2 13 32 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32
  122 2 6 16 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  32 122 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 32 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 32 122 2 5 16 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 32 122 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 32 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 122 2 4 16 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 122 (accept_3_2 7 32 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 122 2 3 16 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 32 122 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 32 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 122 2 2 16 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 122
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 32 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 32 122 2 1 16 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 32 122 (accept_3_2 1 32 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  122)))))))))))))))))))))))))))))))) (allB_succ 31 122 (allA_of_3_0 31 31 122 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 30 122 (allA_succ_of_accept 29 30 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 30 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 122 2 14 15 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 30 122
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 30 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 30 122 2 13 15 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 122 (accept_3_2 25 30 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30
  122 2 12 15 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  30 122 (Polychromatic418967fa.accept_13_10_4_5_1_2331 23 30 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 30 122 2 11 15 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 30 122 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 30 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 122 2 10 15 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 122 (accept_3_2 19 30 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 122 2 9 15 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 122 (Polychromatic418967fa.accept_9_8_3_5_1_241 17
  30 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 122 2 8 15 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 122
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 30 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 30 122 2 7 15 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 30 122 (accept_3_2 13 30 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30
  122 2 6 15 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  30 122 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 30 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 30 122 2 5 15 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 30 122 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 30 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 122 2 4 15 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 122 (accept_3_2 7 30 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 122 2 3 15 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 30 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 30 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 122 2 2 15 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 122
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 30 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 30 122 2 1 15 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 122 (accept_3_2 1 30 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  122)))))))))))))))))))))))))))))) (allB_succ 29 122 (allA_succ_of_accept 28 29 122 (accept_3_2 28 29 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 122
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 29 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 122 (accept_3_2 25 29 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 29 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 122 (accept_3_2 22 29 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 122
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 29 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 122 (accept_3_2 19 29 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 122 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 29 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 122 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 29 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 122 (accept_3_2 16 29 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 122
  (Polychromatic418967fa.accept_13_1_3_5_1_140 14 29 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 122 (accept_3_2 13 29 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 122 (accept_3_2 10 29 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 122
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 122 (accept_3_2 7 29 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  122 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 29 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 122 (accept_3_2 4 29 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  29 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 122 (accept_3_2 1 29 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 122))))))))))))))))))))))))))))) (allB_succ 28 122 (allA_of_3_0
  28 28 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 122 (allA_succ_of_accept 26 27 122
  (Polychromatic418967fa.accept_17_9_10_3_1_3423 26 27 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 122 (accept_3_2 25 27 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 122 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 27 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 122 (accept_3_2 22 27 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 122
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 27 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 122 (accept_3_2 19 27 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 122 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 27 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 122 (accept_3_2 16 27 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 122 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 27 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 122
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 27 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 122 (accept_3_2 13 27 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 122 (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 27 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 122 (accept_3_2 10 27 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 122
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 8 27 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 122 (accept_3_2 7 27 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  122 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 27 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 122 (accept_3_2 4 27 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 122 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 27 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  27 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 122 (accept_3_2 1 27 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 122))))))))))))))))))))))))))) (allB_succ 26 122
  (allA_succ_of_accept 25 26 122 (accept_3_2 25 26 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  122 2 12 13 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 26 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 122 2 11 13 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 26 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 122 2 10 13 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 122 (accept_3_2 19 26 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 122 2 9 13 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 122
  (Polychromatic418967fa.accept_27_17_26_14_1_5915 17 26 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 26 122 2 8 13 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 26 122 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 26 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 122 2 7 13 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 122 (accept_3_2 13 26 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 122 2 6 13 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 26 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 26 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 122 2 5 13 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 122
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 26 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 26 122 2 4 13 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 26 122 (accept_3_2 7 26 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 122
  2 3 13 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26
  122 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 26 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 26 122 2 2 13 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 26 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 26 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 122 2 1 13 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 122 (accept_3_2 1 26 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 26 122)))))))))))))))))))))))))) (allB_succ 25 122 (allA_of_3_0 25 25 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 24 122 (allA_succ_of_accept 23 24 122
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 24 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 122 2 11 12 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 24 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 122 2 10 12 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 122 (accept_3_2 19 24 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 122 2 9 12 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 24 122 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 122 2 8 12 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 122
  (Polychromatic418967fa.accept_20_15_4_2_1_5914 15 24 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 24 122 2 7 12 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 122 (accept_3_2 13 24 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24
  122 2 6 12 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  24 122 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 24 122 2 5 12 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 24 122 (Polychromatic418967fa.accept_18_9_6_14_1_5913 9 24 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 24 122 2 4 12 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 122 (accept_3_2 7 24 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 122 2 3 12 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 24 122 (Polychromatic418967fa.accept_20_5_4_2_1_5912 5 24 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 122 2 2 12 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 24 122
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 24 122 2 1 12 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 24 122 (accept_3_2 1 24 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  122)))))))))))))))))))))))) (allB_succ 23 122 (allA_succ_of_accept 22 23 122 (accept_3_2 22 23 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 122
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 23 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 122 (accept_3_2 19 23 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 122 (Polychromatic418967fa.accept_17_1_6_3_1_4700 18 23 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 122 (accept_3_2 16 23 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 23 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 122
  (Polychromatic418967fa.accept_16_14_7_10_1_898 14 23 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 122 (accept_3_2 13 23 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 122 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 122 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 23 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 122 (accept_3_2 10 23 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 122
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 23 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 122 (accept_3_2 7 23 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  122 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 23 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 122 (accept_3_2 4 23 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 122 (Polychromatic418967fa.accept_13_2_10_5_1_1643
  2 23 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 122 (accept_3_2 1 23
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 122))))))))))))))))))))))) (allB_succ 22 122 (allA_of_3_0 22
  22 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 122 (allA_succ_of_accept 20 21 122
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 21 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 122 (accept_3_2 19 21 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 122 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 21 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 122 (accept_3_2 16 21 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 122
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 14 21 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 122 (accept_3_2 13 21 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 122 (Polychromatic418967fa.accept_13_12_8_5_1_976 12 21 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 122 (accept_3_2 10 21 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 122 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 21 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 122
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 21 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 122 (accept_3_2 7 21 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  122 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 122 (accept_3_2 4 21 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 122 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 21
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 122 (accept_3_2 1 21 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 122))))))))))))))))))))) (allB_succ 20 122 (allA_succ_of_accept
  19 20 122 (accept_3_2 19 20 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 122 2 9 10 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 122
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 20 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 122 2 8 10 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 122 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 20 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 122 2 7 10 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 122 (accept_3_2 13 20 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 122 2 6 10 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 122 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 20 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 122 2 5 10 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 122 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 20
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 122 2 4 10 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 122 (accept_3_2 7 20
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 122 2 3 10 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 122
  (Polychromatic418967fa.accept_12_5_8_2_1_309 5 20 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 122 2 2 10 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 122 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 20 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 122 2 1 10 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 122 (accept_3_2 1 20 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 122)))))))))))))))))))) (allB_succ 19 122 (allA_of_3_0 19 19 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 122 (allA_succ_of_accept 17 18 122 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 18 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 122 2 8 9 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 122
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 18 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 122 2 7 9 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 122 (accept_3_2 13 18 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  122 2 6 9 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 122 (Polychromatic418967fa.accept_19_11_18_8_1_5911 11 18 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 122 2 5 9 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 122 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 18 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 122 2 4 9 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 122 (accept_3_2 7 18 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 122 2 3 9 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 122 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 18 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 122 2 2 9 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 122
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 18 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 122 2 1 9 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 122 (accept_3_2 1 18 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  122)))))))))))))))))) (allB_succ 17 122 (allA_succ_of_accept 16 17 122 (accept_3_2 16 17 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 122
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 17 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 122 (accept_3_2 13 17 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 17 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 122 (accept_3_2 10 17 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 122
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 17 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 122 (accept_3_2 7 17 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  122 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 17 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 122 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 17 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 122 (accept_3_2 4 17 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 122 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  17 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 122 (accept_3_2 1 17 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 122))))))))))))))))) (allB_succ 16 122 (allA_of_3_0 16 16 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 122 (allA_succ_of_accept 14 15 122
  (Polychromatic418967fa.accept_16_14_15_10_1_5910 14 15 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 15 122 (accept_3_2 13 15 122 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 122 (accept_3_2 10 15 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 122
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 15 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 122 (accept_3_2 7 15 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  122 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 15 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 122 (accept_3_2 4 15 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 122 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 15 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 122 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  15 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 122 (accept_3_2 1 15 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 122))))))))))))))) (allB_succ 14 122 (allA_succ_of_accept 13 14
  122 (accept_3_2 13 14 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 122 2 6 7 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 122
  (Polychromatic418967fa.accept_17_11_14_3_1_1427 11 14 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 122 2 5 7 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 122 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 14 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 122 2 4 7 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 122 (accept_3_2 7 14 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 122 2 3 7 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 122 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 14 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 122 2 2 7 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 122 (Polychromatic418967fa.accept_13_3_1_5_1_499 3
  14 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 122 2 1 7 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 122 (accept_3_2 1 14
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 122)))))))))))))) (allB_succ 13 122 (allA_of_3_0 13 13 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 122 (allA_succ_of_accept 11 12 122
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 12 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 122 2 5 6 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 122 2 4 6 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 122 (accept_3_2 7 12 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 122 2 3 6 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 122 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 12 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 122 2 2 6 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 122 (Polychromatic418967fa.accept_15_3_12_2_1_507 3
  12 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 122 2 1 6 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 122 (accept_3_2 1 12
  122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 122)))))))))))) (allB_succ 11 122 (allA_succ_of_accept 10 11
  122 (accept_3_2 10 11 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 122
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 122 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 11 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 122 (accept_3_2 7 11 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 122 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 11 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 122 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 122 (accept_3_2 4 11 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 122 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 122
  (Polychromatic418967fa.accept_17_2_11_3_1_4654 2 11 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 122 (accept_3_2 1 11 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  122))))))))))) (allB_succ 10 122 (allA_of_3_0 10 10 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 122
  (allA_succ_of_accept 8 9 122 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 9 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 122 (accept_3_2 7 9 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 122 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 9 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 122 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 122 (accept_3_2 4 9 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 122
  (Polychromatic418967fa.accept_13_2_9_5_1_959 2 9 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 122 (accept_3_2 1 9 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 122)))))))))
  (allB_succ 8 122 (allA_succ_of_accept 7 8 122 (accept_3_2 7 8 122 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 122 2 3 4 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 122 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 8 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 122 2 2 4 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 122 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 8 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 122 2 1 4 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 122 (accept_3_2 1 8 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 122)))))))) (allB_succ 7 122 (allA_of_3_0 7 7 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 122 (allA_succ_of_accept 5 6 122 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 6
  122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 122 2 2 3 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 122
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 6 122 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 122 2 1 3 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 122 (accept_3_2 1 6 122 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 122))))))
  (allB_succ 5 122 (allA_succ_of_accept 4 5 122 (accept_3_2 4 5 122 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 122 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 122 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 122 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 5 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 122 (accept_3_2 1 5 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 122))))) (allB_succ 4 122 (allA_of_3_0 4 4 122 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 122 (allA_succ_of_accept 2 3 122 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 3 122
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 122 (accept_3_2 1 3 122 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 122))) (allB_succ 2 122 (allA_succ_of_accept 1 2 122 (accept_3_2 1 2 122
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 122)) (allB_two
  122))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


