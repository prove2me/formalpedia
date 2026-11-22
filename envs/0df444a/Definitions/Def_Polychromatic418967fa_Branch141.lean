-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch141
-- name    : Polychromatic418967fa_Branch141
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:15:21.641807+00:00
-- url     : https://prove2.me/theorems/24654ea3-a645-4159-8384-6739c87c424b
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

def Polychromatic418967fa.branch_141 : allB 141 141 :=
  allB_succ' 2 140 141 (Eq.refl Bool.true) (allA_succ_of_accept 1 140 141 (accept_3_4 1 140 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 140 141)) (allB_succ' 3 139 141 (Eq.refl Bool.true) (allA_succ_of_accept 2 139 141
  (accept_3_5 2 139 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 141
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 139 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 139 141))) (allB_succ' 4 138 141 (Eq.refl Bool.true) (allA_succ_of_gcd 3 138 141 3 1 46 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 138 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 138 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 138 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 138 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 138 141)))) (allB_succ' 5 137 141 (Eq.refl Bool.true) (allA_succ_of_accept 4
  137 141 (accept_3_4 4 137 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 137 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 137 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 137 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 141 (accept_3_4 1 137 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 137 141))))) (allB_succ' 6 136 141 (Eq.refl Bool.true) (allA_succ_of_accept 5 136 141
  (accept_3_5 5 136 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 136 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 136 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 136 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 141 (accept_3_5 2 136 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 136 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 136 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 141)))))) (allB_succ' 7 135 141 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 135 141 3 2 45 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 135 141 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 135 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 141 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 135 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 141 3 1 45 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 141 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 135 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 135 141))))))) (allB_succ' 8 134 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 141 (accept_3_4 7 134 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 141 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 134 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 134 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 141 (accept_3_4 4 134 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 134 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 134 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 141 (accept_3_4 1 134 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  141)))))))) (allB_succ' 9 133 141 (Eq.refl Bool.true) (allA_succ_of_accept 8 133 141 (accept_3_5 8 133 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 141 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 133 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 141
  (Polychromatic418967fa.accept_14_6_7_1_1_78 6 133 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 141 (accept_3_5 5 133 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 133 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 133 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 141 (accept_3_5 2 133 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 133 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 141))))))))) (allB_succ' 10 132 141 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 132 141 3 3 44 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 132 141 (Polychromatic418967fa.accept_16_8_4_13_1_1014 8 132 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 141 (Polychromatic418967fa.accept_14_7_6_1_1_1656
  7 132 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 141 3 2 44 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 132 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 132 141 (Polychromatic418967fa.accept_13_4_2_11_1_733 4 132 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 132 141 3 1 44 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 132 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 132 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 141
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 132 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132 141)))))))))) (allB_succ' 11 131 141 (Eq.refl Bool.true) (allA_succ_of_accept 10 131 141 (accept_3_4 10
  131 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 141
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 131 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 131 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 131 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 141 (accept_3_4 7 131 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 131 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 141 (Polychromatic418967fa.accept_15_5_11_6_1_692
  5 131 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 141 (accept_3_4 4
  131 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 131 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 131 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 141 (accept_3_4 1 131 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 131 141))))))))))) (allB_succ' 12 130 141 (Eq.refl Bool.true) (allA_succ_of_accept 11 130 141
  (accept_3_5 11 130 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 130 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 10 130 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 130 141 (Polychromatic418967fa.accept_18_9_4_15_1_555 9 130 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 141 (accept_3_5 8 130 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 130 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 130 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 141 (Polychromatic418967fa.accept_12_6_10_9_1_531
  6 130 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 130 141 (accept_3_5 5
  130 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 130 141
  (Polychromatic418967fa.accept_15_4_10_6_1_2997 4 130 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 130 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 141 (accept_3_5 2 130 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 130 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 130 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 141)))))))))))) (allB_succ' 13 129 141 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 129 141 3 4 43 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 129 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 129 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 129 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 141 3 3 43 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 141
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 129 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 129 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 141 3 2 43 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 129 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 129 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 129 141 3 1 43 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 129 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 129 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 129 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129 141))))))))))))) (allB_succ' 14 128 141
  (Eq.refl Bool.true) (allA_succ_of_accept 13 128 141 (accept_3_4 13 128 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 128 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 128 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 128 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 141 (accept_3_4 10 128 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 141 (Polychromatic418967fa.accept_10_9_8_1_1_1331
  9 128 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 128 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 141 (accept_3_4 7 128 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 128 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 141 (accept_3_4 4 128 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 128 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 141
  (Polychromatic418967fa.accept_11_2_7_9_1_890 2 128 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 141 (accept_3_4 1 128 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  141)))))))))))))) (allB_succ' 15 127 141 (Eq.refl Bool.true) (allA_succ_of_accept 14 127 141 (accept_3_5 14 127 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 141 (Polychromatic418967fa.accept_9_4_1_6_1_284
  13 127 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 127 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 141 (accept_3_5 11 127 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 127 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 141 (Polychromatic418967fa.accept_23_9_12_3_1_7304 9 127 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 141 (accept_3_5 8 127 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 127 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 141 (accept_3_5 5 127 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 127 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 141 (accept_3_5 2 127 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 141 (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 127 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 141))))))))))))))) (allB_succ' 16 126 141 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 126 141 3 5 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 126 141 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 126 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 141
  (Polychromatic418967fa.accept_22_13_16_9_1_7309 13 126 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 126 141 3 4 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 126 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 126 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 141
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 126 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 126 141 3 3 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 126 141 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 126 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 126 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 141 3 2 42 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 141
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 126 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 126 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 126 141 3 1 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 126 141 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 126 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 141
  (Polychromatic418967fa.accept_13_1_9_11_1_703 1 126 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 141)))))))))))))))) (allB_succ' 17 125 141 (Eq.refl Bool.true) (allA_succ_of_accept 16 125 141
  (accept_3_4 16 125 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 141
  (Polychromatic418967fa.accept_12_3_5_9_1_176 15 125 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 125 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 125 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 141 (accept_3_4 13 125 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 125 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 125 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 11
  125 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 141 (accept_3_4 10
  125 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 125 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 125 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 125 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 141 (accept_3_4 7 125 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 125 141 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 125 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 5
  125 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 141 (accept_3_4 4 125
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 141 (Polychromatic418967fa.accept_9_3_8_6_1_80
  3 125 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 125 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 141 (accept_3_4 1 125 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  141))))))))))))))))) (allB_succ' 18 124 141 (Eq.refl Bool.true) (allA_succ_of_accept 17 124 141 (accept_3_5 17 124 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 141
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 16 124 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 124 141 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 124 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 124 141 (accept_3_5 14 124 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 124 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 124 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 12
  124 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 141 (accept_3_5 11
  124 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 10 124 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 124 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 124 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 141 (accept_3_5 8 124 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 124 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 124 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 6
  124 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 141 (accept_3_5 5 124
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 124 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 124 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 124 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 141 (accept_3_5 2 124 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 124 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 141)))))))))))))))))) (allB_succ' 19 123 141 (Eq.refl
  Bool.true) (allA_succ_of_gcd 18 123 141 3 6 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 123 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 123 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 141 (Polychromatic418967fa.accept_15_1_3_6_1_621
  16 123 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 141 3 5 41 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 123 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 123 141 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 123 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 141 3 4 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 141 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  11 123 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 123 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 123 141 3 3 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 123 141 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 123 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 141 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 123 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 141 3 2 41 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 123 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 141 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 123 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 141 3 1 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 123 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 141
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 123 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 123 141))))))))))))))))))) (allB_succ' 20 122 141 (Eq.refl Bool.true) (allA_succ_of_accept 19 122 141
  (accept_3_4 19 122 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 122 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 122 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 122 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 141 (accept_3_4 16 122 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 122 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 141
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 14 122 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 122 141 (accept_3_4 13 122 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 122 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 122 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 141 (accept_3_4 10 122 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 9
  122 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 122 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 141 (accept_3_4 7 122 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 141 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 122 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 122 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 141 (accept_3_4 4 122 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 122 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 141 (accept_3_4 1 122 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  141)))))))))))))))))))) (allB_succ' 21 121 141 (Eq.refl Bool.true) (allA_succ_of_accept 20 121 141 (accept_3_5 20 121
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 141 (Polychromatic418967fa.accept_9_1_4_6_1_5
  19 121 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 141
  (Polychromatic418967fa.accept_15_3_1_6_1_206 18 121 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 141 (accept_3_5 17 121 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 121 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 141 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 121 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 141 (accept_3_5 14 121 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 121 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 141
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 121 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 141 (accept_3_5 11 121 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 121 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 141 (Polychromatic418967fa.accept_15_9_1_6_1_657 9 121 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 141 (accept_3_5 8 121 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 121 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 121 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 141 (accept_3_5 5 121 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 121 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 121 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 141 (accept_3_5 2 121 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 121 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 141))))))))))))))))))))) (allB_succ' 22 120 141
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 120 141 3 7 40 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 120 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 120 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 141
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 120 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 141 3 6 40 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 120 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 120 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 141 3 5 40 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 141
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 120 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 120 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 141 3 4 40 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  120 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 141
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 120 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 120 141 3 3 40 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 120 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 120 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 120 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 141 3 2 40 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 141
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 120 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 120 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 120 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 120 141 3 1 40 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 120 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 120 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 141
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 120 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 141)))))))))))))))))))))) (allB_succ' 23 119 141 (Eq.refl Bool.true) (allA_succ_of_accept 22 119 141
  (accept_3_4 22 119 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 141
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 119 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 119 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 119 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 141 (accept_3_4 19 119 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 119 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 141 (Polychromatic418967fa.accept_9_8_2_6_1_875
  17 119 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 141 (accept_3_4 16
  119 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 141
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 119 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 119 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 119 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 141 (accept_3_4 13 119 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 119 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 119 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 141
  (Polychromatic418967fa.accept_33_11_20_9_1_7308 11 119 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 119 141 (accept_3_4 10 119 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 119 141 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 119 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 119 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 141 (accept_3_4 7 119 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  119 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 119 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 141 (accept_3_4 4 119 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 119 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 141 (accept_3_4 1 119 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119 141))))))))))))))))))))))) (allB_succ' 24 118 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 118 141 (accept_3_5 23 118 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 118 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 118 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 141 (accept_3_5 20 118 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 118 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 141
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 118 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 141 (accept_3_5 17 118 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 118 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 141 (accept_3_5 14 118 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 118 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 118 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 141 (accept_3_5 11 118 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 141 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 118 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 118 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 141 (accept_3_5 8 118 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 141
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 118 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 141 (accept_3_5 5 118 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 118 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 118 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 141 (accept_3_5 2 118 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 118 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 141)))))))))))))))))))))))) (allB_succ' 25 117 141
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 117 141 3 8 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 117 141 (Polychromatic418967fa.accept_18_5_9_15_1_4695 23 117 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 141
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 22 117 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 117 141 3 7 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 117 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 117 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 141 (Polychromatic418967fa.accept_21_19_12_15_1_7307 19
  117 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 141 3 6 39 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 117 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 141 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 117 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 141 3 5 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 141 (Polychromatic418967fa.accept_10_4_7_1_1_471
  14 117 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 117 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 117 141 3 4 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 117 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 117 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 117 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 141 3 3 39 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 141
  (Polychromatic418967fa.accept_16_8_5_13_1_1021 8 117 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 141 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 117 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 141 3 2 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 141 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 117 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 117 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 117 141 3 1 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 117 141 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 117 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 141 (Polychromatic418967fa.accept_16_1_5_13_1_1025 1 117
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117 141)))))))))))))))))))))))))
  (allB_succ' 26 116 141 (Eq.refl Bool.true) (allA_succ_of_accept 25 116 141 (accept_3_4 25 116 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 116 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 116 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 141 (accept_3_4 22 116 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 116 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 116 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 141 (accept_3_4 19 116 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 116 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 116 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 141 (accept_3_4 16 116 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 141 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 116 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 141 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 116 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 141 (accept_3_4 13 116 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 116 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 116 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 141 (accept_3_4 10 116 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 116 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 141 (Polychromatic418967fa.accept_16_8_4_13_1_1014 8 116 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 141 (accept_3_4 7 116 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 116 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 141 (accept_3_4 4 116 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 116 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 116 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 141 (accept_3_4 1 116 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 141)))))))))))))))))))))))))) (allB_succ' 27 115 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 115 141 (accept_3_5 26 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 115 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 141 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 115 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 141 (accept_3_5 23 115 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 115 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 141 (accept_3_5 20 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 115 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 141 (accept_3_5 17 115 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 115 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 141
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 141 (accept_3_5 14 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 115 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 141 (accept_3_5 11 115 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 115 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 141 (accept_3_5 8 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 141 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 141 (accept_3_5 5 115 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 141 (accept_3_5 2 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 115 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 141))))))))))))))))))))))))))) (allB_succ' 28 114 141 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 114 141 3 9 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 114 141 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 114 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 141 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 114
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 141 3 8 38 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 141 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 114 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 114 141 3 7 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 114 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 20
  114 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 114 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 141 3 6 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 114 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 114
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 114 141 3 5 38 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 114 141
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 114 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 114 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 141 3 4 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  114 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 10 114 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 114 141 3 3 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 114 141 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 114 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 141 3 2 38 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 141
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 114 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 114 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 114 141 3 1 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 114 141 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 114 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 141
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 114 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 114 141)))))))))))))))))))))))))))) (allB_succ' 29 113 141 (Eq.refl Bool.true) (allA_succ_of_accept 28 113
  141 (accept_3_4 28 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 141
  (Polychromatic418967fa.accept_12_3_5_9_1_176 27 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 113 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 113 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 141 (accept_3_4 25 113 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 113 141 (Polychromatic418967fa.accept_17_7_11_5_1_3539 24 113 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 141
  (Polychromatic418967fa.accept_17_6_11_5_1_3506 23 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 141 (accept_3_4 22 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 113 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 141 (accept_3_4 19 113 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 141 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 113 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 141 (accept_3_4 16 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 113 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 141 (accept_3_4 13 113 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 113 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 141 (accept_3_4 10 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 141 (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 141 (accept_3_4 7 113 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 141 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 113 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 141
  (Polychromatic418967fa.accept_16_5_1_13_1_1053 5 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 141 (accept_3_4 4 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 113 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 113 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 141 (accept_3_4 1 113 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 141))))))))))))))))))))))))))))) (allB_succ' 30 112 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 112 141 (accept_3_5 29 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 112 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 112 141 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 112 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 141 (accept_3_5 26 112 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 112 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 112 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 112 141
  (Polychromatic418967fa.accept_18_6_4_15_1_2276 24 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 112 141 (accept_3_5 23 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 112 141 (Polychromatic418967fa.accept_13_9_8_11_1_725 22 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 112 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 112 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 112 141 (accept_3_5 20 112 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 112 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 112 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 141
  (Polychromatic418967fa.accept_11_7_2_9_1_480 18 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 112 141 (accept_3_5 17 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 112 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 112 141 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 112 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 141 (accept_3_5 14 112 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 112 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 112 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 112 141 (accept_3_5 11 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 112 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 112 141 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 112 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 141 (accept_3_5 8 112 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 112 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 112 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 141
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 141 (accept_3_5 5 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 141 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 112 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 112 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 141 (accept_3_5 2 112 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 141)))))))))))))))))))))))))))))) (allB_succ' 31 111
  141 (Eq.refl Bool.true) (allA_succ_of_gcd 30 111 141 3 10 37 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 111 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 141
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 111 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 111 141 3 9 37 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 111 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 111 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 141 3 8 37 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 111 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 111 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 141 3 7 37 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  111 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 111 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 111 141 3 6 37 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 111 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 111 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 111 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 141 3 5 37 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 111 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 141 3 4 37 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  111 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 111 141 3 3 37 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 111 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 111 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 111 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 141 3 2 37 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 111 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 111 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 141 3 1 37 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 141
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 111 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111 141))))))))))))))))))))))))))))))) (allB_succ' 32 110 141 (Eq.refl Bool.true) (allA_succ_of_accept 31
  110 141 (accept_3_4 31 110 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 141
  (Polychromatic418967fa.accept_9_3_2_6_1_264 30 110 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 110 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 110 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 141 (accept_3_4 28 110 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 110 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 141 (Polychromatic418967fa.accept_9_8_2_6_1_875
  26 110 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 141 (accept_3_4 25
  110 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 110 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 110 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 141 (accept_3_4 22 110 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 110 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 110 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 141 (Polychromatic418967fa.accept_7_6_5_1_1_416
  20 110 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 141 (accept_3_4 19
  110 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 110 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 110 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 110 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 141 (accept_3_4 16 110 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 110 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 110 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 141 (Polychromatic418967fa.accept_9_5_2_6_1_265
  14 110 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 141 (accept_3_4 13
  110 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 141
  (Polychromatic418967fa.accept_9_3_2_6_1_264 12 110 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 110 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 141 (accept_3_4 10 110 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 110 141 (Polychromatic418967fa.accept_20_9_10_1_1_192 9 110 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 141 (Polychromatic418967fa.accept_9_8_2_6_1_875 8
  110 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 141 (accept_3_4 7 110
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 110 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 110 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 110 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 141 (accept_3_4 4 110 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 110 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 141 (Polychromatic418967fa.accept_19_2_15_8_1_7306
  2 110 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 141 (accept_3_4 1
  110 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110 141)))))))))))))))))))))))))))))))) (allB_succ' 33 109
  141 (Eq.refl Bool.true) (allA_succ_of_accept 32 109 141 (accept_3_5 32 109 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 109 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 109 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 30
  109 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 141 (accept_3_5 29
  109 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 141
  (Polychromatic418967fa.accept_6_4_1_3_1_77 28 109 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 109 141 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 109 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 141 (accept_3_5 26 109 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 109 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 109 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 24
  109 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 141 (accept_3_5 23
  109 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 141
  (Polychromatic418967fa.accept_6_4_1_3_1_77 22 109 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 109 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 109 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 141 (accept_3_5 20 109 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 109 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 109 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 141 (Polychromatic418967fa.accept_10_8_9_1_1_189
  18 109 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 141 (accept_3_5 17
  109 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 141
  (Polychromatic418967fa.accept_6_4_1_3_1_77 16 109 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 109 141 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 109 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 141 (accept_3_5 14 109 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 109 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 109 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 141 (Polychromatic418967fa.accept_7_5_4_1_1_412
  12 109 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 141 (accept_3_5 11
  109 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 141
  (Polychromatic418967fa.accept_6_4_1_3_1_77 10 109 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 109 141 (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 109 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 141 (accept_3_5 8 109 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 109 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 109 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 141 (Polychromatic418967fa.accept_13_6_5_11_1_1971
  6 109 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 141 (accept_3_5 5
  109 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 141
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 109 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 109 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 141 (accept_3_5 2 109 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 109 141 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 109 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109 141))))))))))))))))))))))))))))))))) (allB_succ' 34 108 141
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 141 3 11 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 108 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 108 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 141
  (Polychromatic418967fa.accept_15_1_3_6_1_621 31 108 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 141 3 10 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 141 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 108 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 141
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 28 108 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 108 141 3 9 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 108 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 108 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 108 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 141 3 8 36 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 108 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 141 (Polychromatic418967fa.accept_19_3_13_8_1_4476 22 108 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 108 141 3 7 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 108 141 (Polychromatic418967fa.accept_13_7_4_11_1_1967
  20 108 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 141
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 108 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 141 3 6 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 108 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 108 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 108 141 3 5 36 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 108 141
  (Polychromatic418967fa.accept_19_14_13_8_1_5943 14 108 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 108 141 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 108 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 141 3 4 36 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 108 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 141 (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 108 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 108 141 3 3 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 108 141 (Polychromatic418967fa.accept_13_8_4_11_1_3469
  8 108 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 141
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 108 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 108 141 3 2 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 108 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 108 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 108 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 108 141 3 1 36 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 108 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 108 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 108 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108 141)))))))))))))))))))))))))))))))))) (allB_succ' 35 107 141 (Eq.refl
  Bool.true) (allA_succ_of_accept 34 107 141 (accept_3_4 34 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 107 141 (Polychromatic418967fa.accept_13_7_3_11_1_280 33 107 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 107 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 141 (accept_3_4 31 107 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  107 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 141 (accept_3_4 28 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 141 (accept_3_4 25 107 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 107 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 141 (accept_3_4 22 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 107 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 141 (accept_3_4 19 107 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 141 (accept_3_4 16 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 141 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 141 (accept_3_4 13 107 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 107 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 141 (accept_3_4 10 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 141 (Polychromatic418967fa.accept_18_9_17_15_1_2267 9 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 141 (accept_3_4 7 107 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 141 (accept_3_4 4 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 107 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 141 (accept_3_4 1 107 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 141))))))))))))))))))))))))))))))))))) (allB_succ' 36 106 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 106 141 (accept_3_5 35 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 141 (Polychromatic418967fa.accept_20_14_6_1_1_3023 34 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 106 141 (Polychromatic418967fa.accept_15_3_1_6_1_206 33 106 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 141 (accept_3_5 32 106 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 106 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 141 (accept_3_5 29 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 106 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 141 (accept_3_5 26 106 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 106 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 141
  (Polychromatic418967fa.accept_11_2_7_9_1_890 24 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 141 (accept_3_5 23 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 106 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 141 (accept_3_5 20 106 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 106 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 141
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 141 (accept_3_5 17 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 141 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 141 (accept_3_5 14 106 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 106 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 141 (accept_3_5 11 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 141 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 106 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 141 (accept_3_5 8 106 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 141
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 141 (accept_3_5 5 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 106 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 141 (accept_3_5 2 106 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 106 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 141)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 105 141 (Eq.refl Bool.true) (allA_succ_of_gcd 36 105 141 3 12 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 105 141 (Polychromatic418967fa.accept_13_9_1_11_1_275
  35 105 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 141
  (Polychromatic418967fa.accept_10_4_5_1_1_497 34 105 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 105 141 3 11 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 105 141 (Polychromatic418967fa.accept_23_9_13_3_1_7305 32 105 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 141
  (Polychromatic418967fa.accept_19_12_10_8_1_3270 31 105 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 105 141 3 10 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 105 141 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 105 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 141
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 105 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 105 141 3 9 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 105 141 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 105 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 141 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 105
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 105 141 3 8 35 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 141
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 105 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 105 141 (Polychromatic418967fa.accept_13_9_1_11_1_275 22 105 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 141 3 7 35 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 141
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 105 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 141 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 105 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 141 3 6 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 141 (Polychromatic418967fa.accept_16_1_9_13_1_1822
  17 105 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 141
  (Polychromatic418967fa.accept_10_6_5_1_1_482 16 105 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 105 141 3 5 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 105 141 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 105 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 141 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 105
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 141 3 4 35 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 141
  (Polychromatic418967fa.accept_19_11_10_8_1_7256 11 105 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 105 141 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 105 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 141 3 3 35 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 141
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 8 105 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 141 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 105 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 141 3 2 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 105 141 (Polychromatic418967fa.accept_16_5_9_13_1_3845 5 105 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 141
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 105 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 141 3 1 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 141 (Polychromatic418967fa.accept_17_2_3_5_1_763 2 105 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 141 (Polychromatic418967fa.accept_16_1_9_13_1_1822 1 105
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  141))))))))))))))))))))))))))))))))))))) (allB_succ' 38 104 141 (Eq.refl Bool.true) (allA_succ_of_accept 37 104 141
  (accept_3_4 37 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 141
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 104 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 104 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 141 (accept_3_4 34 104 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 104 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 104 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 141
  (Polychromatic418967fa.accept_23_9_12_3_1_7304 32 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 104 141 (accept_3_4 31 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 104 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 104 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 104 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 141 (accept_3_4 28 104 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 141 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 104 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 141 (accept_3_4 25 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 141 (Polychromatic418967fa.accept_15_9_14_6_1_3004 24 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 104 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 141 (accept_3_4 22 104 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 104 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 141 (accept_3_4 19 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 141 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 104 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 141 (accept_3_4 16 104 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 141 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 104 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 141
  (Polychromatic418967fa.accept_17_14_2_5_1_3560 14 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 141 (accept_3_4 13 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 104 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 141 (accept_3_4 10 104 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 104 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 141 (accept_3_4 7 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 141 (accept_3_4 4 104 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 104 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 141 (accept_3_4 1 104 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  141)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 103 141 (Eq.refl Bool.true) (allA_succ_of_accept 38 103 141
  (accept_3_5 38 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 141
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 103 141 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 103 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 141 (accept_3_5 35 103 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 103 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 141
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 103 141 (accept_3_5 32 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 103 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 103 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 103 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 141 (accept_3_5 29 103 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 141 (accept_3_5 26 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 103 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 141 (accept_3_5 23 103 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 103 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 141 (accept_3_5 20 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 141 (accept_3_5 17 103 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 103 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 141
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 141 (accept_3_5 14 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 103 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 141 (accept_3_5 11 103 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 141
  (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 141 (accept_3_5 8 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 141 (accept_3_5 5 103 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 141 (accept_3_5 2 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 103 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 141))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 102 141 (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 102 141 3 13 34 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 102 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 102 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 102 141 3 12 34 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 102 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 102 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 102 141 3 11 34 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 102 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 141 3 10 34 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 102 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 102 141 3 9 34 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 102 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 102 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 102 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 102 141 3 8 34 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 102 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 141
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 102 141 3 7 34 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 102 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 102 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 102 141 3 6 34 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 102 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 102 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 102 141 3 5 34 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 102 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 141
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 141 3 4 34 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 102 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 102 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 102 141 3 3 34 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 102 141
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 141 3 2 34 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 102 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 141
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 102 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 102 141 3 1 34 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 102 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 102 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 102 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 141))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 101 141 (Eq.refl Bool.true) (allA_succ_of_accept 40 101 141 (accept_3_4 40 101 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 101 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 141 (accept_3_4 37 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 141 (Polychromatic418967fa.accept_17_2_16_5_1_1584 36 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 141 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 101 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 141 (accept_3_4 34 101 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 101 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 141 (accept_3_4 31 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 141 (Polychromatic418967fa.accept_11_7_2_9_1_480 29 101 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 141 (accept_3_4 28 101 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 101
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 141 (accept_3_4 25 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 141 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 101 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 141 (accept_3_4 22 101 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 101 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 141 (accept_3_4 19 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 141 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 101 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 141 (accept_3_4 16 101 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 141 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 101 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 141 (accept_3_4 13 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 101 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 141 (accept_3_4 10 101 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 101 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 141 (accept_3_4 7 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 141 (Polychromatic418967fa.accept_18_6_11_15_1_7255 6 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 101 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 141 (accept_3_4 4 101 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 101 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 141 (accept_3_4 1 101 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  141))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 100 141 (Eq.refl Bool.true) (allA_succ_of_accept 41 100
  141 (accept_3_5 41 100 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 100 141
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 100 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 100 141 (accept_3_5 38 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 100 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 100 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 141 (Polychromatic418967fa.accept_14_8_2_1_1_1652
  36 100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 100 141 (accept_3_5 35
  100 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 100 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 34 100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 100 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 141 (accept_3_5 32 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 100 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 100 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 100 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 30
  100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 100 141 (accept_3_5 29
  100 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 141
  (Polychromatic418967fa.accept_13_2_9_11_1_258 28 100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 100 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 100 141 (accept_3_5 26 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 100 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 100 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 100 141 (Polychromatic418967fa.accept_7_3_2_1_1_225
  24 100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 141 (accept_3_5 23
  100 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 141
  (Polychromatic418967fa.accept_9_4_1_6_1_284 22 100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 100 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 100 141 (accept_3_5 20 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 100 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 100 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 100 141 (Polychromatic418967fa.accept_12_6_4_9_1_544
  18 100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 141 (accept_3_5 17
  100 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 141
  (Polychromatic418967fa.accept_9_7_1_6_1_261 16 100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 100 141 (Polychromatic418967fa.accept_13_2_9_11_1_258 15 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 100 141 (accept_3_5 14 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 100 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 100 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 141 (accept_3_5 11
  100 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 10 100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 100 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 141 (accept_3_5 8 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 100 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 100 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 6
  100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 141 (accept_3_5 5 100
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 141
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 100 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 100 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 141 (accept_3_5 2 100 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 100 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 100 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 141)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 99
  141 (Eq.refl Bool.true) (allA_succ_of_gcd 42 99 141 3 14 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 99 141 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 99 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 141
  (Polychromatic418967fa.accept_13_1_8_11_1_724 40 99 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 99 141 3 13 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 99 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 141 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 99 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 141 3 12 33 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 141
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 99 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99 141 3 11 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 99 141 (Polychromatic418967fa.accept_10_2_9_1_1_185 32
  99 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 141
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 99 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 99 141 3 10 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 99 141 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 99 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 141 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 99 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 141 3 9 33 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 141 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 99 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 99 141 3 8 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 99 141 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 99 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 99 141 3 7 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 99 141 (Polychromatic418967fa.accept_22_20_11_9_1_7303 20 99 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 141 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 99 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 141 3 6 33 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 141
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 99 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 141 (Polychromatic418967fa.accept_13_3_8_11_1_1906 16 99 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 99 141 3 5 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 99 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 141
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 99 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 99 141 3 4 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 99 141 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 99 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 141 3 3 33 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 141
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 99 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 141 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 99 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 141 3 2 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 141 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 99 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 141
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 4 99 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 99 141 3 1 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 99 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 141 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 99 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  141))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 98 141 (Eq.refl Bool.true) (allA_succ_of_accept 43 98
  141 (accept_3_4 43 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 98 141
  (Polychromatic418967fa.accept_12_6_2_9_1_537 42 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 98 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 98 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 141 (accept_3_4 40 98 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 98 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 98 141 (accept_3_4 37 98
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 98 141
  (Polychromatic418967fa.accept_19_17_3_8_1_5946 36 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 98 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 141 (accept_3_4 34 98 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 98 141 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 98 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 141 (Polychromatic418967fa.accept_9_5_8_6_1_281 32
  98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 98 141 (accept_3_4 31 98
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 98 141 (Polychromatic418967fa.accept_9_3_8_6_1_80
  30 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 98 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 98 141 (accept_3_4 28 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  98 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 98 141 (Polychromatic418967fa.accept_17_9_13_5_1_3512 26 98 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 98 141 (accept_3_4 25 98 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 98 141 (Polychromatic418967fa.accept_19_5_3_8_1_7302 24 98 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 98 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 98 141 (accept_3_4 22 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  98 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 98 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 98 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 98 141 (accept_3_4 19 98 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 98 141 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 98 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 98 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 98 141 (accept_3_4 16 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  98 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 98 141 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 98 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 98 141 (accept_3_4 13 98 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 98 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 98 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 98 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 98 141 (accept_3_4 10 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  98 141 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 98 141 (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 98 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 98 141 (accept_3_4 7 98 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 98 141 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 98 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 98 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 98 141 (accept_3_4 4 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 98
  141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 98 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 98 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 141 (accept_3_4 1 98 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 141)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 97 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 97 141 (accept_3_5 44 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 141 (Polychromatic418967fa.accept_13_4_6_11_1_2017 43 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 141 (Polychromatic418967fa.accept_15_12_7_6_1_4013 42 97 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 141 (accept_3_5 41 97 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 141 (accept_3_5 38 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 97 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 141 (accept_3_5 35 97 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 97 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 141 (accept_3_5 32 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 97 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 141 (accept_3_5 29 97 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 141
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 141 (accept_3_5 26 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 141 (Polychromatic418967fa.accept_16_9_1_13_1_1850 25 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 141 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 97 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 141 (accept_3_5 23 97 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 97 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 141 (accept_3_5 20 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 141 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 97 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 141 (accept_3_5 17 97 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 141
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 141 (accept_3_5 14 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 97 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 141 (accept_3_5 11 97 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 97 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 141 (accept_3_5 8 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  141 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 141 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 97 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 141 (accept_3_5 5 97 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 141 (accept_3_5 2 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  141 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 97 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 141))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 96 141 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 96 141 3 15 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 96 141 (Polychromatic418967fa.accept_25_19_21_16_1_7301 44 96 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 141 (Polychromatic418967fa.accept_11_10_8_9_1_492 43 96 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 141 3 14 32 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 141 (Polychromatic418967fa.accept_17_6_11_5_1_3506 40 96 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 96 141 3 13 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 96 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 141
  (Polychromatic418967fa.accept_10_7_6_1_1_486 37 96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 141 3 12 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 96 141 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 96 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 96 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 96 141 3 11 32 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 96 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 96 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 141 3 10 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 141 (Polychromatic418967fa.accept_13_3_5_11_1_716
  29 96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 141
  (Polychromatic418967fa.accept_18_10_6_15_1_3412 28 96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 96 141 3 9 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 96 141 (Polychromatic418967fa.accept_19_7_1_8_1_7300 26 96 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 96 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 141 3 8 32 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 141
  (Polychromatic418967fa.accept_17_6_11_5_1_3506 23 96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 141 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 96 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 96 141 3 7 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 96 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 96 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 141
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 141 3 6 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 96 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 141 (Polychromatic418967fa.accept_13_3_5_11_1_716 16 96 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 96 141 3 5 32 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 96 141
  (Polychromatic418967fa.accept_21_14_12_15_1_7299 14 96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 96 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 96 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 141 3 4 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 11
  96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 10 96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 96 141 3 3 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 96 141 (Polychromatic418967fa.accept_21_8_12_15_1_7298 8 96 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 141 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 96 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 141 3 2 32 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 141
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 96 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 141 3 1 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 141 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 96 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 141
  (Polychromatic418967fa.accept_21_1_12_15_1_2880 1 96 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 141)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 95 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 95 141 (accept_3_4 46 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 141 (accept_3_4 43 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 141
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 41 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 141 (accept_3_4 40 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 141 (accept_3_4 37 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 141 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 95 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 141 (accept_3_4 34 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 141 (accept_3_4 31 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 141 (accept_3_4 28 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 141 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 141 (accept_3_4 25 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 95 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 141
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 23 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 141 (accept_3_4 22 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 141 (accept_3_4 19 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 141 (accept_3_4 16 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 141 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 141 (accept_3_4 13 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 95 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 141 (accept_3_4 10 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 141 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 141 (accept_3_4 7 95 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 141 (accept_3_4 4 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  141 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 95 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 141 (accept_3_4 1 95 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 141))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 94 141 (Eq.refl Bool.true)
  (allA_succ_of_gcd 47 94 141 47 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 46 94 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 94 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 141 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 94 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 94 141 (accept_3_5 44 94 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 94 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 94 141
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 94 141 (accept_3_5 41 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  94 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 94 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 141 (accept_3_5 38 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 94 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 141
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 141 (accept_3_5 35 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 141 (accept_3_5 32 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 141 (accept_3_5 29 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 141 (accept_3_5 26 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 94 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 141
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 141 (accept_3_5 23 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 141 (Polychromatic418967fa.accept_21_1_10_15_1_2828 22 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 141 (accept_3_5 20 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 141 (accept_3_5 17 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 141 (accept_3_5 14 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 94 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 141
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 141 (accept_3_5 11 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 141 (accept_3_5 8 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 141
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 141 (accept_3_5 5 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  141 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 94 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 94 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 141 (accept_3_5 2 94 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 94 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 94 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 141)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  49 93 141 (Eq.refl Bool.true) (allA_succ_of_gcd 48 93 141 3 16 31 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 93 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 93 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 141
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 93 141 3 15 31 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 93 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 93 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 93 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 141 3 14 31 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 93 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 93 141 3 13 31 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 93 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 38
  93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 141
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 93 141 3 12 31 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 93 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 93 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 93 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 141 3 11 31 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 141
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 93 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 141 3 10 31 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 141
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 93 141 3 9 31 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 93 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 93 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 93 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 141 3 8 31 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 141
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 93 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 141 3 7 31 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 93 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 141
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 93 141 3 6 31 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 93 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 93 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 93 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 141 3 5 31 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 141
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 93 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 141 3 4 31 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 93 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 10 93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 93 141 3 3 31 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 93 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 93 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 93 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 141 3 2 31 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 141
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 93 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 141 3 1 31 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 93 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 141
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 93 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 141))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 92 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 92 141 (accept_3_4 49 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 141 (accept_3_4 46 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 141 (Polychromatic418967fa.accept_17_11_7_5_1_1567 45 92 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 141 (accept_3_4 43 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 141 (accept_3_4 40 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 92 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 141
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 38 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 141 (accept_3_4 37 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 141 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 141 (accept_3_4 34 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 92 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 141 (accept_3_4 31 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 141 (accept_3_4 28 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 141 (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 92 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 141 (accept_3_4 25 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 141 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 141 (accept_3_4 22 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 92 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 141
  (Polychromatic418967fa.accept_13_7_1_11_1_732 20 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 141 (accept_3_4 19 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 141 (accept_3_4 16 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 141 (Polychromatic418967fa.accept_16_15_12_13_1_1045 15 92 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 141 (accept_3_4 13 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 141 (accept_3_4 10 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 92 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 141 (accept_3_4 7 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  141 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 141 (accept_3_4 4 92 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 92 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 141 (Polychromatic418967fa.accept_11_2_4_9_1_484 2
  92 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 141 (accept_3_4 1 92 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92 141))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 91 141 (Eq.refl Bool.true) (allA_succ_of_accept 50 91 141 (accept_3_5 50 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 91 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 141 (accept_3_5 47 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 141 (Polychromatic418967fa.accept_17_11_6_5_1_3662 45 91 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 141 (accept_3_5 44 91 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 91 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 141 (accept_3_5 41 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 141 (accept_3_5 38 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 141 (Polychromatic418967fa.accept_15_7_1_6_1_6150 37 91 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 141
  (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 141 (accept_3_5 35 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 141 (Polychromatic418967fa.accept_15_3_1_6_1_206 33 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 141 (accept_3_5 32 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 91 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 141 (accept_3_5 29 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 141 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 141 (accept_3_5 26 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 91 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 141
  (Polychromatic418967fa.accept_15_9_1_6_1_657 24 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 141 (accept_3_5 23 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 141 (accept_3_5 20 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 141 (Polychromatic418967fa.accept_21_19_7_15_1_2848 19 91 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 141 (accept_3_5 17 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 141 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 141 (accept_3_5 14 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 91 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 141 (accept_3_5 11 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 141 (Polychromatic418967fa.accept_15_9_1_6_1_657 9 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 141 (accept_3_5 8 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 91 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 141 (accept_3_5 5 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 141 (accept_3_5 2 91 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 141 (Polychromatic418967fa.accept_17_1_6_5_1_3502 1 91 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 141)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 90 141 (Eq.refl Bool.true) (allA_succ_of_gcd 51 90 141 3 17 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 90 141
  (Polychromatic418967fa.accept_12_2_6_9_1_19 50 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 90 141 (Polychromatic418967fa.accept_13_10_12_11_1_731 49 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 141 3 16 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 141
  (Polychromatic418967fa.accept_12_10_6_9_1_549 46 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 90 141 3 15 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 90 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 141 3 14 30 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 141
  (Polychromatic418967fa.accept_19_3_14_8_1_3272 41 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 90 141 3 13 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 90 141 (Polychromatic418967fa.accept_12_2_6_9_1_19 38
  90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 141 3 12 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 141 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 90 141 3 11 30 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 90 141
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 141 3 10 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 141 (Polychromatic418967fa.accept_11_7_2_9_1_480 29
  90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 141
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 90 141 3 9 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 90 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 141 (Polychromatic418967fa.accept_19_6_14_8_1_3274 25 90
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 141 3 8 30 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 141 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 141 3 7 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 141 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 141 3 6 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 141 (Polychromatic418967fa.accept_13_4_12_11_1_5362 17 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 141 3 5 30 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 141
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 141 (Polychromatic418967fa.accept_19_13_14_8_1_4490 13 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 141 3 4 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 141
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 90 141 3 3 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 90 141 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 141 3 2 30 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 141 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 90 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 141 3 1 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 90 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 141
  (Polychromatic418967fa.accept_13_1_12_11_1_728 1 90 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 141)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 89 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 89 141 (accept_3_4 52 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 141 (accept_3_4 49 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 89 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 141 (accept_3_4 46 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 141 (accept_3_4 43 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 141 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 89 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 141 (accept_3_4 40 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 141 (accept_3_4 37 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 89 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 141
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 141 (accept_3_4 34 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 141 (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 141 (accept_3_4 31 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 89 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 141 (accept_3_4 28 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 141 (accept_3_4 25 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 89 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 141 (accept_3_4 22 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 141 (accept_3_4 19 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 89 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 141 (accept_3_4 16 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 141 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 141 (accept_3_4 13 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 141 (accept_3_4 10 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 141 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 141 (accept_3_4 7 89 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 89 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 141 (accept_3_4 4 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  141 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 89 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 141 (accept_3_4 1 89 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 141))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 88 141 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 88 141 (accept_3_5 53 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 88 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 141 (Polychromatic418967fa.accept_13_12_10_11_1_1279 51 88
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 141 (accept_3_5 50 88 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 49
  88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 141 (accept_3_5 47 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 141 (accept_3_5 44 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 141
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 141 (accept_3_5 41 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 141 (accept_3_5 38 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 141
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 141 (accept_3_5 35 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 141 (Polychromatic418967fa.accept_13_8_10_11_1_2730 34 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 141 (accept_3_5 32 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 141 (accept_3_5 29 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 141 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 88 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 141 (accept_3_5 26 88 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 141 (accept_3_5 23 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 141 (accept_3_5 20 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 141
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 141 (accept_3_5 17 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 141 (Polychromatic418967fa.accept_13_3_10_11_1_1293 16 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 141 (Polychromatic418967fa.accept_13_2_10_11_1_1276 15 88 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 141 (accept_3_5 14 88 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 141 (accept_3_5 11 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 141 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 141 (accept_3_5 8 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 141
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 141 (accept_3_5 5 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  141 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 88 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 141 (accept_3_5 2 88 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 141))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 87 141 (Eq.refl Bool.true) (allA_succ_of_gcd 54 87 141 3 18 29 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 141 (Polychromatic418967fa.accept_11_8_10_9_1_1401 52 87 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 87 141 3 17 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 87 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 141
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 87 141 3 16 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 87 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 87 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 141 3 15 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 141 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 87 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 87 141 3 14 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 87 141 (Polychromatic418967fa.accept_11_8_10_9_1_1401
  41 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 141
  (Polychromatic418967fa.accept_7_5_3_1_1_424 40 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 87 141 3 13 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 87 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 87 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 141 3 12 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 141
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 87 141 3 11 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 87 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 141
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 87 141 3 10 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 87 141 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 87 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 141 (Polychromatic418967fa.accept_13_2_9_11_1_258 28 87 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 141 3 9 29 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 87 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 141 3 8 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 87 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 87 141 3 7 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 87 141 (Polychromatic418967fa.accept_13_7_9_11_1_705 20 87 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 87 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 141 3 6 29 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 141
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 87 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 141 3 5 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 141
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 87 141 3 4 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 87 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 141 3 3 29 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 141
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 141 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 87 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 141 3 2 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 87 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 87 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 141 3 1 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 141 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 87 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  141))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 86 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 86 141 (accept_3_4 55 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 141 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 141 (accept_3_4 52 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 141
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 50 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 141 (accept_3_4 49 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 141 (accept_3_4 46 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 86 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 141 (accept_3_4 43 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 141 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 141 (accept_3_4 40 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 141 (accept_3_4 37 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 141 (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 141 (accept_3_4 34 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 141 (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 86 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 141
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 141 (accept_3_4 31 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 141 (accept_3_4 28 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 141 (accept_3_4 25 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 141 (accept_3_4 22 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 86 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 141 (accept_3_4 19 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 141 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 141 (accept_3_4 16 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 141
  (Polychromatic418967fa.accept_13_1_8_11_1_724 14 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 141 (accept_3_4 13 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 141 (accept_3_4 10 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 141 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 86 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 141 (accept_3_4 7 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  141 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 141 (accept_3_4 4 86 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 141 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  86 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 141 (accept_3_4 1 86 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86 141))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 85 141 (Eq.refl Bool.true) (allA_succ_of_accept 56 85 141 (accept_3_5 56 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 85 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 141
  (Polychromatic418967fa.accept_10_4_5_1_1_497 54 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 141 (accept_3_5 53 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 141 (Polychromatic418967fa.accept_12_3_1_9_1_202 51 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 141 (accept_3_5 50 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 141 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 85 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 141 (accept_3_5 47 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 141 (Polychromatic418967fa.accept_19_7_9_8_1_7297 45 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 141 (accept_3_5 44 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 85 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 141
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 42 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 141 (accept_3_5 41 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 141 (accept_3_5 38 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 85 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 141
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 141 (accept_3_5 35 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 141 (Polychromatic418967fa.accept_15_3_10_6_1_632 33 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 141 (accept_3_5 32 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 141 (Polychromatic418967fa.accept_13_5_7_11_1_3470 31 85 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 141 (accept_3_5 29 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 141 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 141 (accept_3_5 26 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 85 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 141
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 141 (accept_3_5 23 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 141 (accept_3_5 20 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 85 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 141
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 141 (accept_3_5 17 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 141 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 141 (accept_3_5 14 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 141 (Polychromatic418967fa.accept_23_13_16_3_1_7296 13 85 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 141 (accept_3_5 11 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 141 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 141 (accept_3_5 8 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 85 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 141
  (Polychromatic418967fa.accept_10_6_5_1_1_482 6 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 141 (accept_3_5 5 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 141 (accept_3_5 2 85 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 58 84 141 (Eq.refl Bool.true) (allA_succ_of_gcd 57 84 141 3 19 28 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 84 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 84 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 141 3 18 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 53
  84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 84 141 3 17 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 84 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 84 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 141 3 16 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 84 141 3 15 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 84 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 44
  84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 141 3 14 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 84 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 84 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 84 141 3 13 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 84 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 84 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 141 3 12 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 84 141 3 11 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 84 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 84 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 141 3 10 28 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 84 141 3 9 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 84 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 141
  (Polychromatic418967fa.accept_8_1_4_5_1_48 25 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 141 3 8 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 84 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 141 3 7 28 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 84 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 141 3 6 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 84 141 3 5 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 84 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 84 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 141 3 4 28 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 141 3 3 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 84 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 84 141 3 2 28 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 84 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 141 3 1 28 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 84 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 84 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84 141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  59 83 141 (Eq.refl Bool.true) (allA_succ_of_accept 58 83 141 (accept_3_4 58 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 83 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 83 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 56
  83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 141 (accept_3_4 55 83
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 141 (Polychromatic418967fa.accept_4_2_3_1_1_2
  54 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 141 (accept_3_4 52 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 141 (accept_3_4 49 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 83 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 141 (accept_3_4 46 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 141 (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 141 (accept_3_4 43 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 141 (accept_3_4 40 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 141 (accept_3_4 37 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 141 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 83 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 141 (accept_3_4 34 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 141 (accept_3_4 31 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 141
  (Polychromatic418967fa.accept_13_3_5_11_1_716 29 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 141 (accept_3_4 28 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 141 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 141 (accept_3_4 25 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 141 (Polychromatic418967fa.accept_16_8_3_13_1_7295 24 83 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 141 (accept_3_4 22 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 141 (accept_3_4 19 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 141 (accept_3_4 16 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 141 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 141 (accept_3_4 13 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 83 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 141
  (Polychromatic418967fa.accept_17_11_15_5_1_3547 11 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 141 (accept_3_4 10 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 141 (accept_3_4 7 83 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 141 (accept_3_4 4 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  141 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 83 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 141 (accept_3_4 1 83 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 82 141 (Eq.refl
  Bool.true) (allA_succ_of_accept 59 82 141 (accept_3_5 59 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 82 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 82 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 141 (accept_3_5 56 82 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 82 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 55
  82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 141
  (Polychromatic418967fa.accept_12_6_10_9_1_531 54 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 82 141 (accept_3_5 53 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  82 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 82 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 141 (accept_3_5 50 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 82 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 141 (accept_3_5 47 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 141 (accept_3_5 44 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 141
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 141 (accept_3_5 41 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 141 (accept_3_5 38 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 82 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 141
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 141 (accept_3_5 35 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 141 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 141 (accept_3_5 32 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 141 (accept_3_5 29 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 141 (Polychromatic418967fa.accept_13_2_4_11_1_2003 28 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 141 (accept_3_5 26 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 82 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 141 (accept_3_5 23 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 141 (accept_3_5 20 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 141 (accept_3_5 17 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 141 (accept_3_5 14 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 82 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 141 (accept_3_5 11 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 141 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 141 (accept_3_5 8 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 141 (accept_3_5 5 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  141 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 82 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 141 (accept_3_5 2 82 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 82 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 81 141 (Eq.refl Bool.true) (allA_succ_of_gcd 60 81 141 3 20 27 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 141 (Polychromatic418967fa.accept_18_4_9_15_1_3383 58 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 141 3 19 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 141
  (Polychromatic418967fa.accept_21_14_18_15_1_5756 56 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 81 141 (Polychromatic418967fa.accept_21_13_18_15_1_2837 55 81 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 81 141 3 18 27 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 81 141
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 53 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 141 3 17 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 141 (Polychromatic418967fa.accept_19_12_5_8_1_7294
  50 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 141
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 49 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 81 141 3 16 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 81 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 141 (Polychromatic418967fa.accept_11_2_4_9_1_484 46 81 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 81 141 3 15 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 81 141
  (Polychromatic418967fa.accept_8_4_1_5_1_186 44 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 141 (Polychromatic418967fa.accept_17_9_13_5_1_3512 43 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 141 3 14 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 141 (Polychromatic418967fa.accept_13_2_3_11_1_1287
  41 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 40 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 81 141 3 13 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 81 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 141 (Polychromatic418967fa.accept_16_5_1_13_1_1053 37 81
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 81 141 3 12 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 81 141
  (Polychromatic418967fa.accept_11_2_4_9_1_484 35 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 141 (Polychromatic418967fa.accept_13_8_3_11_1_3467 34 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 141 3 11 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 141 (Polychromatic418967fa.accept_14_4_11_1_1_940
  32 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 81 141 3 10 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 81 141 (Polychromatic418967fa.accept_18_11_9_15_1_5988 29 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 81 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 141 3 9 27 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 141 (Polychromatic418967fa.accept_16_9_1_13_1_1850 25 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 141 3 8 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 141 (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 81
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 141
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 22 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 81 141 3 7 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 81 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 81 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 141 3 6 27 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 141 (Polychromatic418967fa.accept_18_16_9_15_1_4614 16 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 141 3 5 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 141 (Polychromatic418967fa.accept_13_1_3_11_1_1289 14 81 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 141
  (Polychromatic418967fa.accept_11_2_4_9_1_484 13 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 81 141 3 4 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 81 141 (Polychromatic418967fa.accept_18_11_9_15_1_5988 11 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 81 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 141 3 3 27 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 141
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 8 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 141 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 141 3 2 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 81 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 141
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 81 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 81 141 3 1 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 81 141 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 81 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 141 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 81 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 80 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 80 141 (accept_3_4 61 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 141 (accept_3_4 58 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 80 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 141 (accept_3_4 55 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 141 (accept_3_4 52 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 80 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 141 (accept_3_4 49 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 141 (accept_3_4 46 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 141 (Polychromatic418967fa.accept_21_3_17_15_1_4199 45 80 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 141 (accept_3_4 43 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 141 (accept_3_4 40 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 80 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 141 (accept_3_4 37 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 141 (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 141 (accept_3_4 34 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 80 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 141 (accept_3_4 31 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 141 (accept_3_4 28 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 141 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 80 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 141
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 141 (accept_3_4 25 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 141 (Polychromatic418967fa.accept_17_7_12_5_1_1580 24 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 141 (accept_3_4 22 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 80 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 141 (accept_3_4 19 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 141 (accept_3_4 16 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 141 (Polychromatic418967fa.accept_19_15_4_8_1_7293 15 80 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 141 (accept_3_4 13 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 141 (accept_3_4 10 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 80 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 141
  (Polychromatic418967fa.accept_17_8_12_5_1_1577 8 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 141 (accept_3_4 7 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  141 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 80 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 141 (accept_3_4 4 80 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 80 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 80
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 141 (accept_3_4 1 80 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 79 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 79 141 (accept_3_5 62 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 141 (Polychromatic418967fa.accept_13_9_1_11_1_275 61 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 141 (Polychromatic418967fa.accept_13_8_1_11_1_1284 60 79 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 141 (accept_3_5 59 79 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 141 (accept_3_5 56 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 141 (accept_3_5 53 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 141
  (Polychromatic418967fa.accept_11_7_2_9_1_480 51 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 141 (accept_3_5 50 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 141 (accept_3_5 47 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 141 (accept_3_5 44 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 141 (Polychromatic418967fa.accept_15_13_4_6_1_3046 43 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 141 (accept_3_5 41 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 141 (accept_3_5 38 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 141 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 79 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 141 (accept_3_5 35 79 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 141
  (Polychromatic418967fa.accept_13_7_1_11_1_732 33 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 141 (accept_3_5 32 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 141 (accept_3_5 29 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 141 (accept_3_5 26 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 141 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 141 (accept_3_5 23 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 141 (accept_3_5 20 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 141 (accept_3_5 17 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 141
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 141 (accept_3_5 14 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 141 (accept_3_5 11 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 141
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 141 (accept_3_5 8 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  141 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 79 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 141 (accept_3_5 5 79 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 79 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  79 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 141 (accept_3_5 2 79 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 79
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 78 141 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 78 141 3 21 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 78 141 (Polychromatic418967fa.accept_12_2_6_9_1_19 62 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 141 (Polychromatic418967fa.accept_15_1_3_6_1_621 61 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78 141 3 20 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 78 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 141 (Polychromatic418967fa.accept_12_10_6_9_1_549 58 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 141 3 19 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 141 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  56 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 141 3 18 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 78 141 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 52 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 78 141 3 17 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 78 141
  (Polychromatic418967fa.accept_12_2_6_9_1_19 50 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 78 141 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 141 3 16 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 141
  (Polychromatic418967fa.accept_12_10_6_9_1_549 46 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 78 141 3 15 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 78 141 (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 141 3 14 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 141
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 41 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 141 3 13 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 141 (Polychromatic418967fa.accept_12_2_6_9_1_19 38
  78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 141
  (Polychromatic418967fa.accept_14_9_8_1_1_2381 37 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 141 3 12 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 78 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 141 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 78 141 3 11 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 78 141
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 78 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 141 3 10 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 141 (Polychromatic418967fa.accept_10_9_8_1_1_1331
  29 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 141
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 78 141 3 9 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 78 141 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 141 (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 78
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 141 3 8 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 141 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 141 3 7 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 141 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 141 3 6 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 141 (Polychromatic418967fa.accept_16_1_14_13_1_3834 17 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 78 141 3 5 26 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 78 141
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 78 141 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 141 3 4 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 141
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 78 141 3 3 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 78 141 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 141 3 2 26 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 141
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 78 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 141 3 1 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 141 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 78 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 141
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 78 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 77 141 (Eq.refl
  Bool.true) (allA_succ_of_accept 64 77 141 (accept_3_4 64 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 77 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 77 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 77 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 77 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 141 (accept_3_4 61 77 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 141 (Polychromatic418967fa.accept_18_6_5_15_1_7292
  60 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 141
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 59 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 141 (accept_3_4 58 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 141 (accept_3_4 55 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 141 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 77 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 141 (accept_3_4 52 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 141 (accept_3_4 49 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 77 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 141 (accept_3_4 46 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 141 (Polychromatic418967fa.accept_18_9_5_15_1_2246 45 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 141 (accept_3_4 43 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 141 (Polychromatic418967fa.accept_15_12_2_6_1_2127 42 77 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 141
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 41 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 141 (accept_3_4 40 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 141 (accept_3_4 37 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 141 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 77 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 141 (accept_3_4 34 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 141 (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 141 (accept_3_4 31 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 77 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 141 (accept_3_4 28 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 141 (accept_3_4 25 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 141 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 77 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 141
  (Polychromatic418967fa.accept_13_10_12_11_1_731 23 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 141 (accept_3_4 22 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 141 (accept_3_4 19 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 141 (Polychromatic418967fa.accept_19_18_1_8_1_7291 18 77 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 141 (accept_3_4 16 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 141 (accept_3_4 13 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 77 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 141 (accept_3_4 10 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 141 (Polychromatic418967fa.accept_18_9_5_15_1_2246 9 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 141 (accept_3_4 7 77 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 141 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 77 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 141
  (Polychromatic418967fa.accept_21_5_14_15_1_7290 5 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 141 (accept_3_4 4 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  141 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 77 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 77 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 141 (accept_3_4 1 77 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 76 141
  (Eq.refl Bool.true) (allA_succ_of_accept 65 76 141 (accept_3_5 65 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 76 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 76 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 141 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 76
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 141 (accept_3_5 62 76 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 61
  76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 141
  (Polychromatic418967fa.accept_18_6_4_15_1_2276 60 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 141 (accept_3_5 59 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 76 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 141 (accept_3_5 56 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 141 (accept_3_5 53 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 141 (accept_3_5 50 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 141 (accept_3_5 47 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 141 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 141 (accept_3_5 44 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 141
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 141 (accept_3_5 41 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 141 (accept_3_5 38 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 141
  (Polychromatic418967fa.accept_16_4_12_13_1_990 36 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 141 (accept_3_5 35 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 141 (accept_3_5 32 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 141 (accept_3_5 29 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 141 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 141 (accept_3_5 26 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 141
  (Polychromatic418967fa.accept_15_9_1_6_1_657 24 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 141 (accept_3_5 23 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 141 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 141 (accept_3_5 20 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 141
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 141 (accept_3_5 17 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 141 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 141 (accept_3_5 14 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 141 (accept_3_5 11 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 141 (accept_3_5 8 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 141
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 141 (accept_3_5 5 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  141 (Polychromatic418967fa.accept_16_4_12_13_1_990 4 76 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 76 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 141 (accept_3_5 2 76 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 75 141 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 75 141 3 22 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 75 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 141 3 21 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 141 3 20 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 59
  75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 141 3 19 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 75 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 141 3 18 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 141 3 17 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 141
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 141 3 16 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 141 3 15 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 141
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 141 3 14 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 41
  75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 141
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 75 141 3 13 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 75 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 141 3 12 25 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 141
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 141 3 11 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 32
  75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 141 3 10 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 75 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 141 3 9 25 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 141 3 8 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 75 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 141 3 7 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 141 3 6 25 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 141 3 5 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 141 3 4 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 141 3 3 25 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 141
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 141 3 2 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 75 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 75 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 141 3 1 25 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 75 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 74 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 74 141 (accept_3_4 67 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  74 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 74 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 141 (accept_3_4 64 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 74 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 141 (accept_3_4 61 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 141 (Polychromatic418967fa.accept_13_8_9_11_1_1265 60 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 141 (accept_3_4 58 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 74 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 141
  (Polychromatic418967fa.accept_23_10_5_3_1_7289 56 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 141 (accept_3_4 55 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 141 (accept_3_4 52 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 141 (accept_3_4 49 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 141 (accept_3_4 46 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 74 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 141 (accept_3_4 43 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 141 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 141 (accept_3_4 40 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 141 (accept_3_4 37 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 141 (Polychromatic418967fa.accept_25_11_24_16_1_7288 36 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 141 (accept_3_4 34 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 74 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 141 (accept_3_4 31 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 141 (accept_3_4 28 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 141 (accept_3_4 25 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 141 (accept_3_4 22 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 74 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 141
  (Polychromatic418967fa.accept_13_7_9_11_1_705 20 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 141 (accept_3_4 19 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 141 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 141 (accept_3_4 16 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 141 (accept_3_4 13 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 141 (accept_3_4 10 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 141 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 74 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 141 (accept_3_4 7 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  141 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 141 (accept_3_4 4 74 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 141 (Polychromatic418967fa.accept_13_2_9_11_1_258 2
  74 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 141 (accept_3_4 1 74 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 73 141 (Eq.refl Bool.true)
  (allA_succ_of_accept 68 73 141 (accept_3_5 68 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  73 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 73 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 66 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 73 141 (accept_3_5 65 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 73 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 73 141
  (Polychromatic418967fa.accept_12_3_1_9_1_202 63 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 73 141 (accept_3_5 62 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  73 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 73 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 73 141 (accept_3_5 59 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 73 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 73 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 73 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 57 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 73 141 (accept_3_5 56 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  73 141 (Polychromatic418967fa.accept_13_3_8_11_1_1906 55 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 73 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 141 (accept_3_5 53 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 73 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 73 141 (accept_3_5 50 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  73 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 73 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 141 (accept_3_5 47 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 73 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 73 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 141
  (Polychromatic418967fa.accept_13_6_8_11_1_5398 45 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 73 141 (accept_3_5 44 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  73 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 73 141 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 141 (accept_3_5 41 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 73 141 (accept_3_5 38 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  73 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 73 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 141 (accept_3_5 35 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 73 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 141
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 73 141 (accept_3_5 32 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 141 (accept_3_5 29 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 141
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 141 (accept_3_5 26 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 141 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 141 (accept_3_5 23 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 73 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 141 (accept_3_5 20 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 141 (accept_3_5 17 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 141
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 141 (accept_3_5 14 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 141 (accept_3_5 11 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 73 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 141 (accept_3_5 8 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  141 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 141 (Polychromatic418967fa.accept_13_6_8_11_1_5398 6 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 141 (accept_3_5 5 73 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 73
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 141 (accept_3_5 2 73 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 141 (Polychromatic418967fa.accept_13_1_8_11_1_724 1
  73 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 72 141 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 72 141 3 23 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 72 141 (Polychromatic418967fa.accept_13_3_7_11_1_1904 68 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 141 (Polychromatic418967fa.accept_15_7_12_6_1_1327 67 72
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 141 3 22 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 141
  (Polychromatic418967fa.accept_15_5_12_6_1_639 65 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 141 (Polychromatic418967fa.accept_13_12_7_11_1_1935 64 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 72 141 3 21 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 72 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 62
  72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 141
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 61 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 141 3 20 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 72 141 (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 72 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 141 3 19 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 141
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 72 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 141 3 18 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 141 (Polychromatic418967fa.accept_10_3_2_1_1_839 53
  72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 52 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 72 141 3 17 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 72 141 (Polychromatic418967fa.accept_14_8_2_1_1_1652 50 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 141 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 72 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 141 3 16 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 141
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 47 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 141 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 72 141 3 15 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 72 141 (Polychromatic418967fa.accept_13_5_7_11_1_3470
  44 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 141
  (Polychromatic418967fa.accept_10_3_2_1_1_839 43 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 141 3 14 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 141 (Polychromatic418967fa.accept_13_1_7_11_1_702 40 72 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 141 3 13 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 72 141 (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 141 3 12 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 141 (Polychromatic418967fa.accept_13_9_7_11_1_1292
  35 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 34 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 72 141 3 11 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 72 141 (Polychromatic418967fa.accept_15_2_12_6_1_3063 32 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 72 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 141 3 10 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 141
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 141 (Polychromatic418967fa.accept_16_12_8_13_1_6073 28 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 72 141 3 9 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 72 141 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 72 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 141
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 141 3 8 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 141 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 141 (Polychromatic418967fa.accept_13_9_7_11_1_1292 22 72
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 141 3 7 24 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 72 141 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 141 3 6 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 72 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 141
  (Polychromatic418967fa.accept_10_6_2_1_1_494 16 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 72 141 3 5 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 72 141 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 72 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 141 3 4 24 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 141
  (Polychromatic418967fa.accept_16_11_8_13_1_3844 11 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 72 141 3 3 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 72 141 (Polychromatic418967fa.accept_14_8_2_1_1_1652 8 72 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 141
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 141 3 2 24 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 141 (Polychromatic418967fa.accept_13_5_7_11_1_3470 5 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 141 (Polychromatic418967fa.accept_13_4_7_11_1_1981 4 72 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 141 3 1 24 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 141
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 72 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 72 141 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 72 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72 141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 141 (allA_succ_of_accept 70 71 141 (accept_3_4 70 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 141 (Polychromatic418967fa.accept_13_4_6_11_1_2017 69 71 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 141 (accept_3_4 67 71 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 66
  71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 65 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 141 (accept_3_4 64 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 141 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 141 (accept_3_4 61 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 141 (Polychromatic418967fa.accept_13_8_6_11_1_1979 60 71 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 141 (accept_3_4 58 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 141 (accept_3_4 55 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 141
  (Polychromatic418967fa.accept_17_2_3_5_1_763 53 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 141 (accept_3_4 52 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 141 (Polychromatic418967fa.accept_11_7_5_9_1_884 51 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 141 (accept_3_4 49 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 71 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 141 (accept_3_4 46 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 141 (Polychromatic418967fa.accept_18_9_17_15_1_2267 45 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 141 (accept_3_4 43 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 141 (accept_3_4 40 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 141 (accept_3_4 37 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 141 (Polychromatic418967fa.accept_16_4_7_13_1_2795 36 71 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 141
  (Polychromatic418967fa.accept_15_5_11_6_1_692 35 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 141 (accept_3_4 34 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 141 (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 141 (accept_3_4 31 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 141 (accept_3_4 28 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 141 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 141 (accept_3_4 25 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 141 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 71 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 141 (accept_3_4 22 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 141 (accept_3_4 19 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 141
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 17 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 141 (accept_3_4 16 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 141 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 141 (accept_3_4 13 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 71 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 141 (accept_3_4 10 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 141 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 141 (accept_3_4 7 71 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 141 (accept_3_4 4 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  141 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 71 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 141 (accept_3_4 1 71 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 141
  (allA_succ_of_accept 69 70 141 (Polychromatic418967fa.accept_20_9_10_1_1_192 69 70 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 70 141 (accept_3_5 68 70 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 70 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 66
  70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 141 (accept_3_5 65 70
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 141 (Polychromatic418967fa.accept_9_1_7_6_1_75
  64 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 141 (accept_3_5 62 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 141 (Polychromatic418967fa.accept_18_6_16_15_1_7287 60 70 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 141 (accept_3_5 59 70 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 70 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 141 (accept_3_5 56 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 141 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 141 (accept_3_5 53 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 141 (Polychromatic418967fa.accept_16_4_6_13_1_1874 52 70 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 141 (accept_3_5 50 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 141 (accept_3_5 47 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 70 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 141
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 141 (accept_3_5 44 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 141 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 141 (accept_3_5 41 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 70 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 141 (accept_3_5 38 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 141 (Polychromatic418967fa.accept_16_4_6_13_1_1874 36 70 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 141 (accept_3_5 35 70 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 141 (Polychromatic418967fa.accept_15_4_10_6_1_2997 34 70
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 141
  (Polychromatic418967fa.accept_13_7_5_11_1_1927 33 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 141 (accept_3_5 32 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 141 (accept_3_5 29 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 70 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 141 (accept_3_5 26 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 141 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 141 (accept_3_5 23 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 70 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 141 (accept_3_5 20 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 141 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 141 (accept_3_5 17 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 141 (Polychromatic418967fa.accept_13_3_5_11_1_716 16 70 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 141 (accept_3_5 14 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 141 (accept_3_5 11 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 70 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 141
  (Polychromatic418967fa.accept_16_9_6_13_1_3831 9 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 141 (accept_3_5 8 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 141 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 70 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 141 (accept_3_5 5 70 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 70 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 70 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 141 (accept_3_5 2 70 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 70
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 141 (allA_succ_of_accept 68 69
  141 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 141 (Polychromatic418967fa.accept_13_2_4_11_1_2003 67 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 141 3 22 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 65
  69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 141
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 64 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 69 141 3 21 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 69 141 (Polychromatic418967fa.accept_10_2_9_1_1_185 62 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 69 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 69 141 3 20 23 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 69 141
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 59 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 69 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 141 3 19 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 141 (Polychromatic418967fa.accept_15_11_9_6_1_1321
  56 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 141
  (Polychromatic418967fa.accept_10_5_9_1_1_187 55 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 69 141 3 18 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 69 141 (Polychromatic418967fa.accept_19_15_12_8_1_5922 53 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 141 (Polychromatic418967fa.accept_10_2_9_1_1_185 52 69 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 69 141 3 17 23 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 69 141
  (Polychromatic418967fa.accept_11_6_3_9_1_906 50 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 141 (Polychromatic418967fa.accept_13_10_4_11_1_1969 49 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 141 3 16 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 47
  69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 141
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 46 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 69 141 3 15 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 69 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 141 (Polychromatic418967fa.accept_19_5_12_8_1_7273 43 69
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 141 3 14 23 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 141
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 41 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 141 3 13 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 141 (Polychromatic418967fa.accept_10_8_9_1_1_189 38
  69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 69 141 3 12 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 69 141 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 141 (Polychromatic418967fa.accept_13_8_4_11_1_3469 34 69
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 141 3 11 23 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 141
  (Polychromatic418967fa.accept_10_2_9_1_1_185 32 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 141 (Polychromatic418967fa.accept_15_1_9_6_1_1323 31 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 141 3 10 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 141 (Polychromatic418967fa.accept_15_14_9_6_1_5093
  29 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 141
  (Polychromatic418967fa.accept_10_8_9_1_1_189 28 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 69 141 3 9 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 69 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 141 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 69 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 141 3 8 23 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 141 (Polychromatic418967fa.accept_10_2_9_1_1_185 22 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 141 3 7 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 141 (Polychromatic418967fa.accept_13_7_4_11_1_1967 20 69 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 69 141 3 6 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 69 141 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 69 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 141 3 5 23 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 141
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 141 (Polychromatic418967fa.accept_21_13_6_15_1_5818 13 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 141 3 4 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 141 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 69 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 141
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 141 3 3 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 141 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 141 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 69 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 141 3 2 23 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 141 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 69 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 141 3 1 23 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 69 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 141
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 69 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 141
  (allA_succ_of_accept 67 68 141 (accept_3_4 67 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  68 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 68 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 141 (accept_3_4 64 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 141 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 68 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 141 (accept_3_4 61 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 141 (accept_3_4 58 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 68 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 141 (accept_3_4 55 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 141 (accept_3_4 52 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 141 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 68 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 141
  (Polychromatic418967fa.accept_19_12_11_8_1_2091 50 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 141 (accept_3_4 49 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 141 (accept_3_4 46 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 68 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 141 (accept_3_4 43 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 141 (accept_3_4 40 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 68 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 141 (accept_3_4 37 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 141 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 141 (accept_3_4 34 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 68 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 141 (accept_3_4 31 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 141 (accept_3_4 28 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 68 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 141 (accept_3_4 25 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 141 (accept_3_4 22 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 68 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 141 (accept_3_4 19 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 141 (accept_3_4 16 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 141 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 68 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 141
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 14 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 141 (accept_3_4 13 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 141 (accept_3_4 10 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 68 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 141 (accept_3_4 7 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  141 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 141 (accept_3_4 4 68 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 68 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 141 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  68 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 141 (accept_3_4 1 68 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 141 (allA_succ_of_accept 66 67
  141 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 141 (accept_3_5 65 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 141 (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 141 (accept_3_5 62 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 67 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 141
  (Polychromatic418967fa.accept_14_4_11_1_1_940 60 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 141 (accept_3_5 59 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 141 (accept_3_5 56 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 67 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 141 (accept_3_5 53 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 141 (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 141 (accept_3_5 50 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 141 (Polychromatic418967fa.accept_13_10_2_11_1_1920 49 67 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 141 (accept_3_5 47 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 141 (accept_3_5 44 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 67 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 141 (accept_3_5 41 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 141 (accept_3_5 38 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 67 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 141
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 141 (accept_3_5 35 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 141 (accept_3_5 32 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 67 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 141 (accept_3_5 29 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 141 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 141 (accept_3_5 26 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 67 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 141 (accept_3_5 23 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 141 (accept_3_5 20 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 67 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 141 (accept_3_5 17 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 141 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 141 (accept_3_5 14 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 141 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 67 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 141 (accept_3_5 11 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 141 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 141 (accept_3_5 8 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 141 (accept_3_5 5 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 67 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 141 (accept_3_5 2 67 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 67 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 141 (allA_succ_of_accept 65 66
  141 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 141 3 21 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 62
  66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 141
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 141 3 20 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 66 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 66 141 3 19 22 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 66 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 141 3 18 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 66 141 3 17 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 66 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 66 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 141 3 16 22 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 141 3 15 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 44
  66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 141 3 14 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 66 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 66 141 3 13 22 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 141 3 12 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 66 141 3 11 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 66 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 141 3 10 22 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 141 3 9 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 66 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 141 3 8 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 66 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 141 3 7 22 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 141 3 6 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 66 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 141 3 5 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 66 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 141 3 4 22 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 141 3 3 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 66 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 141 3 2 22 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 66 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 141 3 1 22 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 66 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 66 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 141 (allA_succ_of_accept 64 65 141 (accept_3_4 64 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 65 141 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 65 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 65 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 141 (accept_3_4 61 65 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 60
  65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 141 (accept_3_4 58 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 141 (accept_3_4 55 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 141 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 65 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 141 (accept_3_4 52 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 141 (accept_3_4 49 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 65 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 141
  (Polychromatic418967fa.accept_25_22_15_16_1_7286 47 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 65 141 (accept_3_4 46 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 65 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 65 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 141 (accept_3_4 43 65 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 141 (Polychromatic418967fa.accept_15_12_5_6_1_2148
  42 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 141 (accept_3_4 40 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 141 (accept_3_4 37 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 65 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 141 (accept_3_4 34 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 141 (Polychromatic418967fa.accept_15_3_5_6_1_4005 33 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 141 (accept_3_4 31 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 65 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 141
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 141 (accept_3_4 28 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 141 (accept_3_4 25 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 65 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 141 (accept_3_4 22 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 141 (accept_3_4 19 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 141 (Polychromatic418967fa.accept_15_3_5_6_1_4005 18 65 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 141 (accept_3_4 16 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 141 (accept_3_4 13 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 65 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 141
  (Polychromatic418967fa.accept_15_11_5_6_1_669 11 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 141 (accept_3_4 10 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 141 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 141 (accept_3_4 7 65 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 65 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 141 (accept_3_4 4 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  141 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 65 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 65 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 141 (accept_3_4 1 65 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 141
  (allA_succ_of_accept 63 64 141 (Polychromatic418967fa.accept_14_7_8_1_1_1621 63 64 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 64 141 (accept_3_5 62 64 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 64 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 141 (Polychromatic418967fa.accept_17_9_13_5_1_3512
  60 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 141 (accept_3_5 59
  64 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 141
  (Polychromatic418967fa.accept_9_4_1_6_1_284 58 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 64 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 64 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 141 (accept_3_5 56 64 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 64 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 141 (Polychromatic418967fa.accept_12_6_4_9_1_544
  54 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 141 (accept_3_5 53
  64 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 141
  (Polychromatic418967fa.accept_9_7_1_6_1_261 52 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 64 141 (Polychromatic418967fa.accept_14_9_8_1_1_2381 51 64 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 141 (accept_3_5 50 64 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 64 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 48
  64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 141 (accept_3_5 47 64
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 141
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 46 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 64 141 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 64 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 141 (accept_3_5 44 64 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 64 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 141 (Polychromatic418967fa.accept_12_6_4_9_1_544
  42 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 141 (accept_3_5 41
  64 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 141
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 64 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 64 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 141 (accept_3_5 38 64 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 64 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 141
  (Polychromatic418967fa.accept_13_10_12_11_1_731 36 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 64 141 (accept_3_5 35 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  64 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 64 141 (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 64 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 141 (accept_3_5 32 64 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 64 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 64 141 (accept_3_5 29 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  64 141 (Polychromatic418967fa.accept_15_13_4_6_1_3046 28 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 64 141 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 141 (accept_3_5 26 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 64 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 141
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 64 141 (accept_3_5 23 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  64 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 64 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 141 (accept_3_5 20 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 141
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 141 (accept_3_5 17 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  64 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 141 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 141 (accept_3_5 14 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 141 (accept_3_5 11 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 141 (Polychromatic418967fa.accept_13_10_12_11_1_731 10 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 141 (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 141 (accept_3_5 8 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 141
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 141 (accept_3_5 5 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  141 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 64 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 64 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 64 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 141 (accept_3_5 2 64 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 64 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 141 (allA_succ_of_accept 62 63 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 141 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 141 3 20 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 141 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  59 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 141 3 19 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 141 (Polychromatic418967fa.accept_15_11_3_6_1_1306 56 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 141 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 63 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 141 3 18 21 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 141
  (Polychromatic418967fa.accept_12_5_3_9_1_541 53 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 141 (Polychromatic418967fa.accept_10_2_3_1_1_481 52 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 141 3 17 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 141
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 63 141 3 16 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 141 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 141 3 15 21 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 141
  (Polychromatic418967fa.accept_16_12_15_13_1_3872 44 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 63 141 (Polychromatic418967fa.accept_11_10_8_9_1_492 43 63 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 141 3 14 21 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 141
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 141 (Polychromatic418967fa.accept_15_10_3_6_1_3042 40 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 141 3 13 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 141
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 63 141 3 12 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 63 141 (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 141 3 11 21 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 141
  (Polychromatic418967fa.accept_10_2_3_1_1_481 32 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 141 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 141 3 10 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 141 (Polychromatic418967fa.accept_12_5_3_9_1_541 29
  63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 141
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 63 141 3 9 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 141 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 63 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 141 3 8 21 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 141
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 141 3 7 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 141 (Polychromatic418967fa.accept_14_6_7_1_1_78 20 63 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 141
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 63 141 3 6 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 63 141 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 141 (Polychromatic418967fa.accept_15_1_3_6_1_621 16 63 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 141 3 5 21 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 141 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 141 3 4 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 141 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 63 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 141 3 3 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 141 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 141 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 63 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 141 3 2 21 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 141
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 141 (Polychromatic418967fa.accept_18_4_9_15_1_3383 4 63 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 141 3 1 21 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 141
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 63 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 141))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 141 (allA_succ_of_accept
  61 62 141 (accept_3_4 61 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 141
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 141 (accept_3_4 58 62 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 56
  62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 141 (accept_3_4 55 62
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 62 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 141 (accept_3_4 52 62 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 141 (Polychromatic418967fa.accept_9_5_8_6_1_281 50
  62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 141 (accept_3_4 49 62
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 141 (Polychromatic418967fa.accept_9_3_8_6_1_80
  48 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 62 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 62 141 (accept_3_4 46 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  62 141 (Polychromatic418967fa.accept_30_15_2_21_1_7285 45 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 62 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 141 (accept_3_4 43 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 141 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 62 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 62 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 62 141 (accept_3_4 40 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  62 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 62 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 141 (accept_3_4 37 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 141 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 62 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 141 (accept_3_4 34 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  62 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 62 141 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 141 (accept_3_4 31 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 62 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 141 (accept_3_4 28 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 141 (accept_3_4 25 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 141 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 62 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 141 (accept_3_4 22 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 141 (accept_3_4 19 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 141 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 62 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 141 (accept_3_4 16 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 141 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 141 (accept_3_4 13 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 62 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 141 (accept_3_4 10 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 62 141 (Polychromatic418967fa.accept_13_8_10_11_1_2730 8 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 141 (accept_3_4 7 62 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 141 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 62 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 141 (accept_3_4 4 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 62 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 141 (accept_3_4 1 62 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 141
  (allA_succ_of_accept 60 61 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 61 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 61 141 (accept_3_5 59 61 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 61 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 61 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 57
  61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 141 (accept_3_5 56 61
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 61 141 (Polychromatic418967fa.accept_13_2_9_11_1_258 54 61 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 61 141 (accept_3_5 53 61 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 61 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 61 141 (Polychromatic418967fa.accept_12_3_1_9_1_202
  51 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 141 (accept_3_5 50
  61 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 141
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 61 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 61 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 61 141 (accept_3_5 47 61 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 61 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 61 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 45
  61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 141 (accept_3_5 44 61
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 141
  (Polychromatic418967fa.accept_19_5_4_8_1_2080 43 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 61 141 (Polychromatic418967fa.accept_22_20_17_9_1_7284 42 61 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 61 141 (accept_3_5 41 61 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 61 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 39
  61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 141 (accept_3_5 38 61
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 141 (Polychromatic418967fa.accept_9_1_7_6_1_75
  37 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 141
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 141 (accept_3_5 35 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 141 (Polychromatic418967fa.accept_13_7_9_11_1_705 33 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 141 (accept_3_5 32 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 61 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 141 (accept_3_5 29 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 141 (accept_3_5 26 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 61 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 141 (accept_3_5 23 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 141 (accept_3_5 20 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 61 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 141 (accept_3_5 17 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 141 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 141 (accept_3_5 14 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 61 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 141 (accept_3_5 11 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 141 (Polychromatic418967fa.accept_15_9_1_6_1_657 9 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 141 (accept_3_5 8 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 141 (Polychromatic418967fa.accept_13_7_9_11_1_705 7 61 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 141 (accept_3_5 5 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 61 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 141 (accept_3_5 2 61 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 61 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 141 (allA_succ_of_accept 59 60 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 60 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 141
  (Polychromatic418967fa.accept_13_6_8_11_1_5398 58 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 141 3 19 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 141 (Polychromatic418967fa.accept_13_4_8_11_1_1937 56 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 141 (Polychromatic418967fa.accept_13_3_8_11_1_1906 55 60
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 141 3 18 20 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 141
  (Polychromatic418967fa.accept_13_1_8_11_1_724 53 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 60 141 3 17 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 60 141 (Polychromatic418967fa.accept_21_8_18_15_1_5812
  50 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 141
  (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 141 3 16 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 141 (Polychromatic418967fa.accept_17_12_9_5_1_799 46 60 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 141 3 15 20 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 141
  (Polychromatic418967fa.accept_19_6_3_8_1_7283 44 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 141 (Polychromatic418967fa.accept_13_4_8_11_1_1937 43 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 141 3 14 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 41
  60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 40 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 60 141 3 13 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 60 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 141 (Polychromatic418967fa.accept_21_16_18_15_1_7282 37 60
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 141 3 12 20 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 141
  (Polychromatic418967fa.accept_13_9_8_11_1_725 35 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 141 (Polychromatic418967fa.accept_18_16_6_15_1_3376 34 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 141 3 11 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 141 (Polychromatic418967fa.accept_13_6_8_11_1_5398
  32 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 141 3 10 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 141 (Polychromatic418967fa.accept_11_7_5_9_1_884 29 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 141 (Polychromatic418967fa.accept_18_10_6_15_1_3412 28 60
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 141 3 9 20 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 60 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 141 3 8 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 141 (Polychromatic418967fa.accept_13_10_8_11_1_1985 23 60
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 141
  (Polychromatic418967fa.accept_13_9_8_11_1_725 22 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 60 141 3 7 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 60 141 (Polychromatic418967fa.accept_16_4_12_13_1_990 20 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 60 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 141 3 6 20 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 141 (Polychromatic418967fa.accept_13_3_8_11_1_1906 16 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 141 3 5 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 141 (Polychromatic418967fa.accept_13_1_8_11_1_724 14 60 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 141
  (Polychromatic418967fa.accept_17_13_9_5_1_6022 13 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 141 3 4 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 141 (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 60 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 60 141 3 3 20 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 141
  (Polychromatic418967fa.accept_16_8_12_13_1_3851 8 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 141 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 141 3 2 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 60 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 141
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 4 60 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 60 141 3 1 20 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 60 141 (Polychromatic418967fa.accept_21_2_18_15_1_4236 2 60 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 60 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 141 (allA_succ_of_accept 58 59 141
  (accept_3_4 58 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 141
  (Polychromatic418967fa.accept_9_3_5_6_1_253 57 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 141 (accept_3_4 55 59 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 141 (accept_3_4 52 59
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 141 (Polychromatic418967fa.accept_7_2_3_1_1_10
  51 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 141 (accept_3_4 49 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 141 (accept_3_4 46 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 141 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 59 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 141 (accept_3_4 43 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 141 (Polychromatic418967fa.accept_27_14_5_6_1_7281 41 59 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 141 (accept_3_4 40 59 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 59 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 141 (accept_3_4 37 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 141 (Polychromatic418967fa.accept_24_12_11_21_1_7280 36 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 141 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 141 (accept_3_4 34 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 59 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 141 (accept_3_4 31 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 141 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 141 (accept_3_4 28 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 141 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 59 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 141 (accept_3_4 25 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 141 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 141 (accept_3_4 22 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 59 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 141 (accept_3_4 19 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 141 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 141 (accept_3_4 16 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 141 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 59 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 141 (accept_3_4 13 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 141 (accept_3_4 10 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 59 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 141 (accept_3_4 7 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 59 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 141 (accept_3_4 4 59 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 59 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 141 (accept_3_4 1 59 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 58 141 (allA_succ_of_accept 57 58 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 58 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 141 (accept_3_5 56 58 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 58 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 141
  (Polychromatic418967fa.accept_12_6_10_9_1_531 54 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 58 141 (accept_3_5 53 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  58 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 58 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 141 (accept_3_5 50 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 58 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 58 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 58 141 (accept_3_5 47 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  58 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 141 (accept_3_5 44 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 141
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 141 (accept_3_5 41 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 141 (Polychromatic418967fa.accept_19_2_1_8_1_7279 40 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 141 (accept_3_5 38 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 58 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 141
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 141 (accept_3_5 35 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 141 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 141 (accept_3_5 32 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 141 (accept_3_5 29 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 141 (accept_3_5 26 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 58 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 141 (accept_3_5 23 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 141 (Polychromatic418967fa.accept_14_8_2_1_1_1652 22 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 141 (accept_3_5 20 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 141
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 141 (accept_3_5 17 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 141 (accept_3_5 14 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 58 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 141 (accept_3_5 11 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 141 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 141 (accept_3_5 8 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 141 (accept_3_5 5 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  141 (Polychromatic418967fa.accept_13_4_6_11_1_2017 4 58 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 58 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 141 (accept_3_5 2 58 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 58 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 141 (allA_succ_of_accept 56 57 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 141 3 18 19 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 53
  57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 141
  (Polychromatic418967fa.accept_8_4_1_5_1_186 52 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 141 3 17 19 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 57 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 141 3 16 19 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 141 3 15 19 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 44
  57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 141 3 14 19 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 57 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 141 3 13 19 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 141 3 12 19 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 141 3 11 19 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 57 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 141 3 10 19 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 141 3 9 19 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 57 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 141 3 8 19 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 57 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 141 3 7 19 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 141
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 141 3 6 19 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 57 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 141 3 5 19 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 57 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 141 3 4 19 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 141 3 3 19 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 141 3 2 19 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 57 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 141 3 1 19 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 57 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 141))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 141 (allA_succ_of_accept 55 56 141 (accept_3_4 55 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 141 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 56 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 141 (accept_3_4 52 56 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 141
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 51 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 56 141 (Polychromatic418967fa.accept_9_5_2_6_1_265 50 56 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 56 141 (accept_3_4 49 56 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 56 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 56 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 56 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 47
  56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 141 (accept_3_4 46 56
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 141
  (Polychromatic418967fa.accept_10_5_6_1_1_836 45 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 56 141 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 56 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 56 141 (accept_3_4 43 56 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 56 141 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 56 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 56 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 41
  56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 141 (accept_3_4 40 56
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 141
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 56 141 (Polychromatic418967fa.accept_13_12_4_11_1_1925 38 56 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 141 (accept_3_4 37 56 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 56 141 (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 56 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 56 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 56 141 (accept_3_4 34 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  56 141 (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 56 141 (Polychromatic418967fa.accept_9_5_2_6_1_265 32 56 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 141 (accept_3_4 31 56 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 56 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 56 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 56 141 (accept_3_4 28 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  56 141 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 56 141 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 56 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 141 (accept_3_4 25 56 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 56 141 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 56 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 56 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 56 141 (accept_3_4 22 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  56 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 56 141 (Polychromatic418967fa.accept_13_7_4_11_1_1967 20 56 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 141 (accept_3_4 19 56 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 56 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 56 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 56 141 (accept_3_4 16 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  56 141 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 56 141 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 56 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 56 141 (accept_3_4 13 56 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 56 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 56 141 (accept_3_4 10 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  56 141 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 56 141 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 56 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 56 141 (accept_3_4 7 56 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 56 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 56 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 56 141 (accept_3_4 4 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56
  141 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 56 141 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 56 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 141 (accept_3_4 1 56 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 141)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 141
  (allA_succ_of_accept 54 55 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 141 (accept_3_5 53 55 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 51
  55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 141 (accept_3_5 50 55
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 141
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 55 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 141 (accept_3_5 47 55 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 141 (Polychromatic418967fa.accept_20_5_15_1_1_7278
  45 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 141 (accept_3_5 44
  55 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 141
  (Polychromatic418967fa.accept_9_7_1_6_1_261 43 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 55 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 141 (accept_3_5 41 55 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 55 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 39
  55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 141 (accept_3_5 38 55
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 141 (Polychromatic418967fa.accept_7_2_6_1_1_73
  37 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 141
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 141 (accept_3_5 35 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 141 (accept_3_5 32 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 55 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 141 (accept_3_5 29 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 141 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 141 (accept_3_5 26 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 55 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 141
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 141 (accept_3_5 23 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 141 (accept_3_5 20 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 55 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 141 (accept_3_5 17 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 141 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 141 (accept_3_5 14 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 55 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 141 (accept_3_5 11 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 141 (accept_3_5 8 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 141 (accept_3_5 5 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 55 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 141 (accept_3_5 2 55 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 141 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 55 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 141)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 141 (allA_succ_of_accept 53 54 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 54 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 52 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 54 141 3 17 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 54 141 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 54 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 141 (Polychromatic418967fa.accept_13_10_2_11_1_1920 49 54
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 141 3 16 18 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 54 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 141 3 15 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 141 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  44 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 141 3 14 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 54 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 54 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 54 141 3 13 18 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 54 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 141 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 54 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 141 3 12 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 34 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 54 141 3 11 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 54 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 54 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 141 3 10 18 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 141
  (Polychromatic418967fa.accept_13_3_2_11_1_1999 29 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 54 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 141 3 9 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 141 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 54 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 141 3 8 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 141 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 54 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 141 3 7 18 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 141 3 6 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 54 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 141
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 54 141 3 5 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 54 141 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 54 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 54 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 141 3 4 18 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 54 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 141 3 3 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 141 (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 54 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 141 3 2 18 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 141 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 54 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 54 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 141 3 1 18 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 141
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 54 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 141 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 54 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 141)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  141 (allA_succ_of_accept 52 53 141 (accept_3_4 52 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 53 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 141 (accept_3_4 49 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 53 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 141 (accept_3_4 46 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 141 (accept_3_4 43 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 141 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 53 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 141 (accept_3_4 40 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 141 (accept_3_4 37 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 141 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 53 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 141
  (Polychromatic418967fa.accept_13_9_1_11_1_275 35 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 141 (accept_3_4 34 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 141 (accept_3_4 31 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 53 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 141 (accept_3_4 28 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 141 (accept_3_4 25 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 53 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 141 (accept_3_4 22 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 141 (accept_3_4 19 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 141 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 53 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 141 (accept_3_4 16 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 141 (accept_3_4 13 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 141
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 141 (accept_3_4 10 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 141 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 141 (accept_3_4 7 53 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 141 (Polychromatic418967fa.accept_18_6_17_15_1_4603 6 53 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 141 (accept_3_4 4 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  141 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 53 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 53 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 141 (accept_3_4 1 53 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 141))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 141
  (allA_succ_of_accept 51 52 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 52 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 141 (accept_3_5 50 52 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 48
  52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 141 (accept_3_5 47 52
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 141 (Polychromatic418967fa.accept_7_4_3_1_1_87
  46 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 52 141
  (Polychromatic418967fa.accept_18_9_16_15_1_2241 45 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 52 141 (accept_3_5 44 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  52 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 52 141 (Polychromatic418967fa.accept_12_6_4_9_1_544 42 52 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 141 (accept_3_5 41 52 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 52 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 52 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 52 141 (accept_3_5 38 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  52 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 52 141 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 52 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 141 (accept_3_5 35 52 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 141 (Polychromatic418967fa.accept_23_11_6_3_1_7277 34 52 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 141
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 141 (accept_3_5 32 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 52 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 141 (accept_3_5 29 52 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 52 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 141
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 52 141 (accept_3_5 26 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  52 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 52 141 (Polychromatic418967fa.accept_16_8_4_13_1_1014 24 52 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 141 (accept_3_5 23 52 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 52 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 141 (accept_3_5 20 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 52 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 141 (accept_3_5 17 52 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 52 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 141
  (Polychromatic418967fa.accept_28_15_24_1_1_7276 15 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 141 (accept_3_5 14 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  52 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 52 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 52 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 141 (accept_3_5 11 52 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 52 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 141 (accept_3_5 8 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52
  141 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 52 141 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 52 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 141 (accept_3_5 5 52 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 52 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 52 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 141 (accept_3_5 2 52 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  141)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 141 (allA_succ_of_accept 50 51 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 141 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 51 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 141 3 16 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 141 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  47 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 141 3 15 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 141 (Polychromatic418967fa.accept_19_6_13_8_1_4508 44 51 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 141 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 51 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 141 3 14 17 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 141 (Polychromatic418967fa.accept_13_1_12_11_1_728 40 51 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 141 3 13 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 141
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 141 3 12 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 141 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 51 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 141 3 11 17 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 141
  (Polychromatic418967fa.accept_20_12_11_1_1_3032 32 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 51 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 141 3 10 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 141 (Polychromatic418967fa.accept_12_5_3_9_1_541 29
  51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 141
  (Polychromatic418967fa.accept_20_8_11_1_1_7275 28 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 141 3 9 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 141 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 51 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 141 3 8 17 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 141
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 141 3 7 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 51 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 141
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 141 3 6 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 51 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 141 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 51 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 141 3 5 17 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 51 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 141 3 4 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 141 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 51 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 141 3 3 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 141 (Polychromatic418967fa.accept_14_8_9_1_1_3313 8 51 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 141 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 51 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 141 3 2 17 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 141
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 141 (Polychromatic418967fa.accept_13_4_12_11_1_5362 4 51 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 141 3 1 17 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 141
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 51 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 141))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 141 (allA_succ_of_accept 49 50 141
  (accept_3_4 49 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 141
  (Polychromatic418967fa.accept_9_3_5_6_1_253 48 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 141 (accept_3_4 46 50 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 141 (Polychromatic418967fa.accept_17_11_16_5_1_3612 45 50 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 141 (accept_3_4 43 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 141 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 141 (accept_3_4 40 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 141 (accept_3_4 37 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 141 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 141 (accept_3_4 34 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 141 (Polychromatic418967fa.accept_15_3_5_6_1_4005 33 50 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 141
  (Polychromatic418967fa.accept_26_6_24_11_1_7274 32 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 141 (accept_3_4 31 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 141 (accept_3_4 28 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 141 (accept_3_4 25 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 141 (Polychromatic418967fa.accept_19_5_12_8_1_7273 24 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 141 (accept_3_4 22 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 50 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 141 (accept_3_4 19 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 141 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 141 (accept_3_4 16 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 141
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 141 (accept_3_4 13 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 141 (accept_3_4 10 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 141 (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 50 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 141 (accept_3_4 7 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  141 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 50 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 141 (accept_3_4 4 50 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 141 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  50 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 141 (accept_3_4 1 50 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 141)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 141 (allA_succ_of_accept 48 49 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 141 (accept_3_5 47 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 49 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 141
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 141 (accept_3_5 44 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 141 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 141 (accept_3_5 41 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 141 (accept_3_5 38 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 141 (accept_3_5 35 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 49 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 141
  (Polychromatic418967fa.accept_21_12_7_15_1_7272 33 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 141 (accept_3_5 32 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 141 (Polychromatic418967fa.accept_19_12_11_8_1_2091 31 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 141 (accept_3_5 29 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 141
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 141 (accept_3_5 26 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 141 (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 141 (accept_3_5 23 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 49 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 141 (accept_3_5 20 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 141 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 141 (accept_3_5 17 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 141
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 141 (accept_3_5 14 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 141 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 141 (accept_3_5 11 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 49 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 141
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 141 (accept_3_5 8 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  141 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 141 (Polychromatic418967fa.accept_14_6_7_1_1_78 6 49 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 141 (accept_3_5 5 49 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  49 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 141 (accept_3_5 2 49 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  141))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 141 (allA_succ_of_accept 47 48 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 48 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 141 3 15 16 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 44
  48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 141 3 14 16 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 48 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 48 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 48 141 3 13 16 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 48 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 48 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 48 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 141 3 12 16 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 48 141 3 11 16 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 48 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 48 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 48 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 141 3 10 16 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 48 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 141 3 9 16 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 48 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 141 3 8 16 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 48 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 48 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 141 3 7 16 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 48 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 48 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 141 3 6 16 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 48 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 16 48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 48 141 3 5 16 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 48 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 48 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 141 3 4 16 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 48 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 141 3 3 16 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 48 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 141 3 2 16 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 48 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 141 3 1 16 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 48 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 48 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 48 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 141)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 141
  (allA_succ_of_accept 46 47 141 (accept_3_4 46 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 141 (accept_3_4 43 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 141 (accept_3_4 40 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 141 (accept_3_4 37 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 141 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 47 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 141 (accept_3_4 34 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 141 (Polychromatic418967fa.accept_19_14_9_8_1_7271 33 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 141 (accept_3_4 31 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 141
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 29 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 141 (accept_3_4 28 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 141 (accept_3_4 25 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 47 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 141 (accept_3_4 22 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 141 (accept_3_4 19 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 141 (accept_3_4 16 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 141 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 141 (accept_3_4 13 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 141 (accept_3_4 10 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 141 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 141 (accept_3_4 7 47 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 141 (accept_3_4 4 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  141 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 47 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 141 (accept_3_4 1 47 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 141))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 141 (allA_succ_of_accept 45
  46 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 46 141 (accept_3_5 44 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 46 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 141 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 46 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 141 (accept_3_5 41 46 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 40
  46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 141 (accept_3_5 38 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 141 (Polychromatic418967fa.accept_20_16_6_1_1_7270 36 46 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 141 (accept_3_5 35 46 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 46 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 141 (accept_3_5 32 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 46 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 141 (accept_3_5 29 46 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 141 (Polychromatic418967fa.accept_25_3_21_16_1_7269 28 46 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 141 (accept_3_5 26 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 46 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 141 (accept_3_5 23 46 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 46 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 141 (accept_3_5 20 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 141 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 46 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 141 (accept_3_5 17 46 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 46 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 141 (accept_3_5 14 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 46 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 141 (accept_3_5 11 46 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 46 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 141
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 141 (accept_3_5 8 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 141 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 46 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 141 (accept_3_5 5 46 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 46 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 141 (accept_3_5 2 46 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 46
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  141)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 141 (allA_succ_of_accept 44 45 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 45 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 141 (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 45 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 141 3 14 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 141 (Polychromatic418967fa.accept_17_7_11_5_1_3539
  41 45 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 141
  (Polychromatic418967fa.accept_7_5_3_1_1_424 40 45 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 141 3 13 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 141 (Polychromatic418967fa.accept_21_17_3_15_1_5762 38 45 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 45 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 141 3 12 15 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 141
  (Polychromatic418967fa.accept_18_17_9_15_1_7268 35 45 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 141 (Polychromatic418967fa.accept_10_4_5_1_1_497 34 45 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 141 3 11 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  45 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 141
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 31 45 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 141 3 10 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 141 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 45 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 141 (Polychromatic418967fa.accept_18_10_9_15_1_7267 28 45
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 141 3 9 15 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 141
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 45 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 45 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 141 3 8 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 45 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 141
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 22 45 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 141 3 7 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 141 (Polychromatic418967fa.accept_19_1_7_8_1_3262 20 45 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 45 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 141 3 6 15 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 141
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 17 45 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 45 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 141 3 5 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 141 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 45 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 141
  (Polychromatic418967fa.accept_22_13_1_9_1_7266 13 45 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 141 3 4 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 45 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 141 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 45
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 141 3 3 15 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 141
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 8 45 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 141 (Polychromatic418967fa.accept_17_7_11_5_1_3539 7 45 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 141 3 2 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 45 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 45 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 141 3 1 15 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 45 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 141 (Polychromatic418967fa.accept_19_1_7_8_1_3262 1 45 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  141))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 141 (allA_succ_of_accept 43 44 141 (accept_3_4 43 44
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 141
  (Polychromatic418967fa.accept_12_6_8_9_1_553 42 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 141 (accept_3_4 40 44 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 44 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 38
  44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 141 (accept_3_4 37 44
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 141
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 141 (accept_3_4 34 44 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 44 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 141 (Polychromatic418967fa.accept_9_5_8_6_1_281 32
  44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 141 (accept_3_4 31 44
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 141 (Polychromatic418967fa.accept_9_3_8_6_1_80
  30 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 141 (accept_3_4 28 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 141 (Polychromatic418967fa.accept_16_10_12_13_1_4950 26 44 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 141 (accept_3_4 25 44 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 44 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 44 141 (accept_3_4 22 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  44 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 44 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 44 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 141 (accept_3_4 19 44 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 44 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 141 (accept_3_4 16 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  44 141 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 44 141 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 44 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 141 (accept_3_4 13 44 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 44 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 44 141 (accept_3_4 10 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  44 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 44 141 (Polychromatic418967fa.accept_14_8_2_1_1_1652 8 44 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 141 (accept_3_4 7 44 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 44 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 141 (accept_3_4 4 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  141 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 44 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 44 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 141 (accept_3_4 1 44 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 141)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 141 (allA_succ_of_accept 42 43
  141 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 141 (accept_3_5 41 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 43 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 141 (accept_3_5 38 43 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 43 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 141
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 141 (accept_3_5 35 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 141 (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 43 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 141 (accept_3_5 32 43 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 43 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 141 (accept_3_5 29 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 141 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 43 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 141 (accept_3_5 26 43 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 141 (Polychromatic418967fa.accept_13_12_4_11_1_1925 25 43 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 141
  (Polychromatic418967fa.accept_16_8_11_13_1_7265 24 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 141 (accept_3_5 23 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 43 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 141 (accept_3_5 20 43 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 43 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 141 (accept_3_5 17 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 141 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 43 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 141 (accept_3_5 14 43 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 43 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 141 (accept_3_5 11 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 141 (Polychromatic418967fa.accept_25_9_18_16_1_7264 9 43 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 141 (accept_3_5 8 43 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 141 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 43 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 141 (accept_3_5 5 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 43 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 141 (accept_3_5 2 43 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 43 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 141))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 141
  (allA_succ_of_accept 41 42 141 (Polychromatic418967fa.accept_13_2_3_11_1_1287 41 42 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 42 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 141 3 13 14 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 141
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 42 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 141 (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 42 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 141 3 12 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  42 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 141
  (Polychromatic418967fa.accept_12_10_6_9_1_549 34 42 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 42 141 3 11 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 42 141 (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 42 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 141 3 10 14 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 141
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 42 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 42 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 42 141 3 9 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 141 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 42 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 141
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 42 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 141 3 8 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 141 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 42 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 141 3 7 14 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 141
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 42 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 141 3 6 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 141 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 42 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 141
  (Polychromatic418967fa.accept_10_6_2_1_1_494 16 42 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 42 141 3 5 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 42 141 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 42 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 141 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 42 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 141 3 4 14 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 141 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 42 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 141 3 3 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 141 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 42 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 141 3 2 14 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 141 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 42 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 42 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 141 3 1 14 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 141
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 42 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 141 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 42 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 141)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 141
  (allA_succ_of_accept 40 41 141 (accept_3_4 40 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 41 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 141 (accept_3_4 37 41 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 41 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 141 (accept_3_4 34 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 141 (accept_3_4 31 41 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 41 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 141 (accept_3_4 28 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 41 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 141 (accept_3_4 25 41 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 141 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 41 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 141 (accept_3_4 22 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 141 (accept_3_4 19 41 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 141 (Polychromatic418967fa.accept_15_3_11_6_1_3083 18 41 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 141 (accept_3_4 16 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 41 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 141 (accept_3_4 13 41 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 41 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 141 (accept_3_4 10 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 141 (accept_3_4 7 41 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 141 (Polychromatic418967fa.accept_16_6_9_13_1_2751 6 41 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 141 (accept_3_4 4 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  141 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 41 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 41 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 141 (accept_3_4 1 41 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 141))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 141 (allA_succ_of_accept 39 40 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 141 (accept_3_5 38 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 141 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 40 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 141 (accept_3_5 35 40 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 40 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 141
  (Polychromatic418967fa.accept_13_7_1_11_1_732 33 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 141 (accept_3_5 32 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 40 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 141 (accept_3_5 29 40 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 40 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 141 (accept_3_5 26 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 40 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 141 (accept_3_5 23 40 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 141 (Polychromatic418967fa.accept_13_9_1_11_1_275 22 40 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 141 (accept_3_5 20 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 40 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 141 (accept_3_5 17 40 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 40 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 141
  (Polychromatic418967fa.accept_19_15_2_8_1_7263 15 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 141 (accept_3_5 14 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 40 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 141 (accept_3_5 11 40 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 40 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 141
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 141 (accept_3_5 8 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  141 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 40 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 141 (accept_3_5 5 40 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 40 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 40
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 141 (accept_3_5 2 40 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  141)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 141 (allA_succ_of_accept 38 39 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 39 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 141 3 12 13 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  39 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 141 3 11 13 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 39 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 141 3 10 13 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 39 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 141 3 9 13 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 39 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 141 3 8 13 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 39 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 141 3 7 13 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 39 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 39 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 141 3 6 13 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 39 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 39 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 141 3 5 13 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 39 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 141 3 4 13 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 141 3 3 13 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 39 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 141 3 2 13 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 39 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 141 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 141 3 1 13 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 39 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 141))))))))))))))))))))))))))))))))))))))) (allB_succ 38 141
  (allA_succ_of_accept 37 38 141 (accept_3_4 37 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 141 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 141 (accept_3_4 34 38 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 38 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 141 (accept_3_4 31 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 38 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 141 (accept_3_4 28 38 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 141
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 141 (accept_3_4 25 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 141 (Polychromatic418967fa.accept_21_3_17_15_1_4199 24 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 141 (accept_3_4 22 38 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 38 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 141
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 20 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 141 (accept_3_4 19 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 38 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 141 (accept_3_4 16 38 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 141 (accept_3_4 13 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 141 (accept_3_4 10 38 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 38 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 141 (accept_3_4 7 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  141 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 38 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 38 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 141 (accept_3_4 4 38 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 38
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 141 (accept_3_4 1 38 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 141)))))))))))))))))))))))))))))))))))))) (allB_succ 37 141
  (allA_succ_of_accept 36 37 141 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 37 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 141 (accept_3_5 35 37 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 37 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 141 (Polychromatic418967fa.accept_16_1_5_13_1_1025
  33 37 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 141 (accept_3_5 32
  37 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 37 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 37 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 141 (accept_3_5 29 37 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 27
  37 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 141 (accept_3_5 26 37
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 141
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 37 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 141 (accept_3_5 23 37 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 37 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  37 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 141 (accept_3_5 20 37
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 141
  (Polychromatic418967fa.accept_17_2_3_5_1_763 19 37 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 141 (Polychromatic418967fa.accept_16_2_5_13_1_3842 18 37 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 141 (accept_3_5 17 37 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 141 (Polychromatic418967fa.accept_12_3_1_9_1_202
  15 37 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 141 (accept_3_5 14
  37 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 37 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 37 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 37 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 141 (accept_3_5 11 37 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 37 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 37 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 141 (Polychromatic418967fa.accept_16_9_5_13_1_4972
  9 37 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 141 (accept_3_5 8 37
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 141 (Polychromatic418967fa.accept_9_7_1_6_1_261
  7 37 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 37 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 141 (accept_3_5 5 37 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 37 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 141 (accept_3_5 2 37 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 141 (Polychromatic418967fa.accept_15_1_7_6_1_6127 1 37 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 141))))))))))))))))))))))))))))))))))))) (allB_succ 36 141
  (allA_succ_of_accept 35 36 141 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 36 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 141 (Polychromatic418967fa.accept_13_8_10_11_1_2730 34 36
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 141 3 11 12 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 141
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 36 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 141 (Polychromatic418967fa.accept_17_14_2_5_1_3560 31 36 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 141 3 10 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 141 (Polychromatic418967fa.accept_13_3_10_11_1_1293
  29 36 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 141
  (Polychromatic418967fa.accept_11_6_3_9_1_906 28 36 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 36 141 3 9 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 36 141 (Polychromatic418967fa.accept_20_6_16_1_1_7262 26 36 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 36 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 141 3 8 12 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 141
  (Polychromatic418967fa.accept_14_9_8_1_1_2381 23 36 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 141 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 36 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 141 3 7 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 141 (Polychromatic418967fa.accept_17_3_2_5_1_2556 20 36 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 141
  (Polychromatic418967fa.accept_22_19_14_9_1_7261 19 36 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 141 3 6 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 36 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 141 (Polychromatic418967fa.accept_13_3_10_11_1_1293 16 36
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 141 3 5 12 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 141
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 36 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 141 (Polychromatic418967fa.accept_25_13_11_16_1_7260 13 36 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 141 3 4 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 141 (Polychromatic418967fa.accept_19_11_17_8_1_7259 11 36
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 141
  (Polychromatic418967fa.accept_19_10_17_8_1_5917 10 36 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 36 141 3 3 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 36 141 (Polychromatic418967fa.accept_13_8_10_11_1_2730 8 36 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 141 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 36 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 141 3 2 12 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 141
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 36 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 141 (Polychromatic418967fa.accept_13_4_10_11_1_1908 4 36 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 141 3 1 12 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 141 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 36 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 141
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 141)))))))))))))))))))))))))))))))))))) (allB_succ 35 141 (allA_succ_of_accept 34 35 141 (accept_3_4 34
  35 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 141
  (Polychromatic418967fa.accept_13_7_9_11_1_705 33 35 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 141 (accept_3_4 31 35 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 29
  35 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 141 (accept_3_4 28 35
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 141
  (Polychromatic418967fa.accept_12_3_11_9_1_193 27 35 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 141 (accept_3_4 25 35 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 141 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 35 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 141 (Polychromatic418967fa.accept_9_5_8_6_1_281 23
  35 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 141 (accept_3_4 22 35
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 141 (Polychromatic418967fa.accept_9_3_8_6_1_80
  21 35 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 141 (accept_3_4 19 35 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 141 (Polychromatic418967fa.accept_16_1_3_13_1_2785 17 35 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 141 (accept_3_4 16 35 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 141 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 35 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 141 (accept_3_4 13 35 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 35 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 141 (accept_3_4 10 35 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 141 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 35 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 141
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 141 (accept_3_4 7 35 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 141 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 35 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 141 (accept_3_4 4 35 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 35 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 141 (accept_3_4 1 35 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 141))))))))))))))))))))))))))))))))))) (allB_succ 34 141
  (allA_succ_of_accept 33 34 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 34 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 141 (accept_3_5 32 34 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 34 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 30
  34 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 141 (accept_3_5 29 34
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 141 (Polychromatic418967fa.accept_9_1_7_6_1_75
  28 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 141 (accept_3_5 26 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 141 (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 34 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 141 (accept_3_5 23 34 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 34 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 141
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 141 (accept_3_5 20 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 141 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 34 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 141 (accept_3_5 17 34 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 34 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 141 (accept_3_5 14 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 34 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 141 (accept_3_5 11 34 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 34 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 141
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 141 (accept_3_5 8 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 141 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 34 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 141 (accept_3_5 5 34 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 34 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 141 (accept_3_5 2 34 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 34
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 141))))))))))))))))))))))))))))))))))
  (allB_succ 33 141 (allA_succ_of_accept 32 33 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 33 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 33 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 141 3 10 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 141 (Polychromatic418967fa.accept_13_3_7_11_1_1904 29 33 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 141 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 33 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 141 3 9 11 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 141
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 33 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 33 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 141 3 8 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 141 (Polychromatic418967fa.accept_19_4_14_8_1_4510 23 33 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 141
  (Polychromatic418967fa.accept_10_2_3_1_1_481 22 33 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 141 3 7 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 33 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 141 (Polychromatic418967fa.accept_16_3_1_13_1_4968 19 33
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 141 3 6 11 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 141
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 33 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 141 (Polychromatic418967fa.accept_13_3_7_11_1_1904 16 33 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 141 3 5 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 141 (Polychromatic418967fa.accept_13_1_7_11_1_702 14 33 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 33 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 141 3 4 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 33 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 33 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 141 3 3 11 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 141
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 33 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 141 (Polychromatic418967fa.accept_19_7_14_8_1_4535 7 33 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 141 3 2 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 141 (Polychromatic418967fa.accept_13_5_7_11_1_3470 5 33 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 141
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 33 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 141 3 1 11 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 141 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 33 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 141 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 33 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 141)))))))))))))))))))))))))))))))))
  (allB_succ 32 141 (allA_succ_of_accept 31 32 141 (accept_3_4 31 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 32 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 141 (accept_3_4 28 32 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 141 (Polychromatic418967fa.accept_15_12_2_6_1_2127
  27 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 141 (accept_3_4 25 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 141 (accept_3_4 22 32 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 141
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 141 (accept_3_4 19 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 141 (accept_3_4 16 32 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 141 (Polychromatic418967fa.accept_24_15_8_21_1_7258 15 32 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 141
  (Polychromatic418967fa.accept_19_14_13_8_1_5943 14 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 141 (accept_3_4 13 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 141 (accept_3_4 10 32 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 141 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 32 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 141
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 141 (accept_3_4 7 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  141 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 32 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 141 (accept_3_4 4 32 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 32 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 141 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  32 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 141 (accept_3_4 1 32 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 141)))))))))))))))))))))))))))))))) (allB_succ 31 141
  (allA_succ_of_accept 30 31 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 141 (accept_3_5 29 31 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 141 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  27 31 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 141 (accept_3_5 26
  31 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 31 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 141 (Polychromatic418967fa.accept_15_9_1_6_1_657 24 31 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 141 (accept_3_5 23 31 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 21
  31 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 141 (accept_3_5 20 31
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 141
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 141 (accept_3_5 17 31 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 141 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  15 31 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 141 (accept_3_5 14
  31 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 141
  (Polychromatic418967fa.accept_24_13_7_21_1_7257 13 31 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 141 (accept_3_5 11 31 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 31
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 141 (accept_3_5 8 31 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 7
  31 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 141 (accept_3_5 5 31 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 31 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 141 (accept_3_5 2 31 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 31 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 141))))))))))))))))))))))))))))))) (allB_succ 30 141
  (allA_succ_of_accept 29 30 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 30 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 30 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 141 3 9 10 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 141
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 30 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 30 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 141 3 8 10 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 141
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 30 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 141 3 7 10 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 30 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 141 3 6 10 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 141
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 30 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 30 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 141 3 5 10 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 30 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 141
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 30 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 141 3 4 10 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 30 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 141 3 3 10 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 141
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 30 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 141 3 2 10 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 30 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 141
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 30 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 141 3 1 10 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 30 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 30 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 141)))))))))))))))))))))))))))))) (allB_succ
  29 141 (allA_succ_of_accept 28 29 141 (accept_3_4 28 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 141 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 29 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 29 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 141 (accept_3_4 25 29 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 141 (Polychromatic418967fa.accept_11_2_7_9_1_890
  24 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 141 (accept_3_4 22 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 141 (accept_3_4 19 29 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 141 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 29 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 141 (accept_3_4 16 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 141 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 29 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 141 (accept_3_4 13 29 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 29 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 141
  (Polychromatic418967fa.accept_19_11_10_8_1_7256 11 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 141 (accept_3_4 10 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 141 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 141 (accept_3_4 7 29 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 141 (Polychromatic418967fa.accept_18_6_11_15_1_7255 6 29 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 141 (accept_3_4 4 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  141 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 29 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 29 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 141 (accept_3_4 1 29 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 141))))))))))))))))))))))))))))) (allB_succ 28 141 (allA_succ_of_accept 27 28 141
  (Polychromatic418967fa.accept_18_9_10_15_1_7254 27 28 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 141 (accept_3_5 26 28 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 141 (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 28 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 141 (accept_3_5 23 28 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 28 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 28 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 141 (accept_3_5 20 28 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 141 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 28 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 141 (accept_3_5 17 28 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 28 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 141
  (Polychromatic418967fa.accept_16_15_12_13_1_1045 15 28 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 28 141 (accept_3_5 14 28 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 28 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 141 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 28 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 141 (accept_3_5 11 28 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 141
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 10 28 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 28 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 28 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 141 (accept_3_5 8 28 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 28 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 141 (Polychromatic418967fa.accept_12_6_4_9_1_544 6
  28 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 141 (accept_3_5 5 28 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 141 (Polychromatic418967fa.accept_9_4_1_6_1_284 4
  28 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 141 (accept_3_5 2 28 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28
  141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 141)))))))))))))))))))))))))))) (allB_succ 27 141 (allA_succ_of_accept 26 27 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 141 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 27 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 141 3 8 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 27 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 141 3 7 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 141 (Polychromatic418967fa.accept_13_7_1_11_1_732 20 27 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 27 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 141 3 6 9 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 141
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 27 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 27 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 141 3 5 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 141
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 27 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 141 3 4 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 141 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 27 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 141 3 3 9 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 141
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 8 27 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 141 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 27 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 141 3 2 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 27 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 141
  (Polychromatic418967fa.accept_10_4_7_1_1_471 4 27 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 141 3 1 9 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 141 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 27 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 141))))))))))))))))))))))))))) (allB_succ 26
  141 (allA_succ_of_accept 25 26 141 (accept_3_4 25 26 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 26 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 26 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 141 (accept_3_4 22 26 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 26 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 141
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 26 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 141 (accept_3_4 19 26 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 26 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 26 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 141 (accept_3_4 16 26 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 141
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 26 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 141 (accept_3_4 13 26 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  26 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 26 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 141 (accept_3_4 10 26 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 141 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 26 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 141
  (Polychromatic418967fa.accept_21_8_5_15_1_4208 8 26 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 141 (accept_3_4 7 26 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  141 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 26 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 26 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 141 (accept_3_4 4 26 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 26
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 141 (accept_3_4 1 26 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 141)))))))))))))))))))))))))) (allB_succ 25 141
  (allA_succ_of_accept 24 25 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 25 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 141 (accept_3_5 23 25 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 25 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  25 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 141 (accept_3_5 20 25
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 141
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 25 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 141 (Polychromatic418967fa.accept_14_4_11_1_1_940 18 25 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 141 (accept_3_5 17 25 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 141 (Polychromatic418967fa.accept_12_3_1_9_1_202
  15 25 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 141 (accept_3_5 14
  25 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 141
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 25 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 25 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 141 (accept_3_5 11 25 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 25 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 25 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 141 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9
  25 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 141 (accept_3_5 8 25 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 141 (Polychromatic418967fa.accept_13_7_12_11_1_1911
  7 25 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 141
  (Polychromatic418967fa.accept_10_6_5_1_1_482 6 25 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 141 (accept_3_5 5 25 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 25 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 141 (accept_3_5 2 25 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 25 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 141))))))))))))))))))))))))) (allB_succ 24 141
  (allA_succ_of_accept 23 24 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 141 (Polychromatic418967fa.accept_18_4_6_15_1_2250 22 24
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 141 3 7 8 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 141
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 20 24 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 24 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 141 3 6 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 141 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 24 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 24 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 141 3 5 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 141 (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 24 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 141 (Polychromatic418967fa.accept_19_13_5_8_1_4487 13 24
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 141 3 4 8 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 141 (Polychromatic418967fa.accept_18_10_6_15_1_3412 10 24 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 141 3 3 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 141 (Polychromatic418967fa.accept_21_8_3_15_1_2875 8 24 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 141
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 24 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 141 3 2 8 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 141 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 24 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 141 3 1 8 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 141
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 24 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 141 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 24 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 141)))))))))))))))))))))))) (allB_succ 23 141 (allA_succ_of_accept 22 23
  141 (accept_3_4 22 23 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 141
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 23 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 141 (accept_3_4 19 23 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  23 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 141 (accept_3_4 16 23
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 141
  (Polychromatic418967fa.accept_12_3_11_9_1_193 15 23 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 141 (accept_3_4 13 23 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 141 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 23 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 141 (Polychromatic418967fa.accept_9_2_5_6_1_536 11
  23 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 141 (accept_3_4 10 23
  141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 141
  (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 23 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 141 (accept_3_4 7 23 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 141 (Polychromatic418967fa.accept_19_5_4_8_1_2080 5
  23 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 141 (accept_3_4 4 23 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  23 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 141 (accept_3_4 1 23 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  141))))))))))))))))))))))) (allB_succ 22 141 (allA_succ_of_accept 21 22 141
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 22 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 141 (accept_3_5 20 22 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 141 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 22 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 141 (accept_3_5 17 22 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 22 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 141
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 141 (accept_3_5 14 22 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 22 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 22 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 141 (accept_3_5 11 22 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 22 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 141
  (Polychromatic418967fa.accept_10_9_2_1_1_840 9 22 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 141 (accept_3_5 8 22 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 141 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 22 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 141 (accept_3_5 5 22 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 141 (Polychromatic418967fa.accept_16_4_6_13_1_1874 4 22 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 141 (accept_3_5 2 22 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 22
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 141)))))))))))))))))))))) (allB_succ 21
  141 (allA_succ_of_accept 20 21 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 21 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 141 3 6 7 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 141
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 141 3 5 7 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 21 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 141
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 141 3 4 7 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 21 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 21 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 141 3 3 7 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 141
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 141 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 21 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 141 3 2 7 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 141
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 141 3 1 7 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 141 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 21 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 141 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 141))))))))))))))))))))) (allB_succ 20 141
  (allA_succ_of_accept 19 20 141 (accept_3_4 19 20 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 141 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 20 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 141 (accept_3_4 16 20 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 20 141 (Polychromatic418967fa.accept_19_15_1_8_1_4520 15 20 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 141
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 20 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 20 141 (accept_3_4 13 20 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  20 141 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 20 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 20 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 141 (accept_3_4 10 20 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 20 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 20 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 141
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 20 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 20 141 (accept_3_4 7 20 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20
  141 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 20 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 141 (accept_3_4 4 20 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 141 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 20 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 20
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 141 (accept_3_4 1 20 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 141)))))))))))))))))))) (allB_succ 19 141 (allA_succ_of_accept
  18 19 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 141 (accept_3_5 17 19 141 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 141 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 19 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 141 (accept_3_5 14 19 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 141 (Polychromatic418967fa.accept_7_6_5_1_1_416 13
  19 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 141
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 19 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 141 (accept_3_5 11 19 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 141 (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 19 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 141 (accept_3_5 8 19 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 141 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 141 (accept_3_5 5 19 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 19 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 141 (accept_3_5 2 19 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 141 (Polychromatic418967fa.accept_16_1_3_13_1_2785 1 19 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 141))))))))))))))))))) (allB_succ 18 141 (allA_succ_of_accept 17
  18 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 18 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 141 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 18 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 141 3 5 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 141 (Polychromatic418967fa.accept_12_2_6_9_1_19 14
  18 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 141
  (Polychromatic418967fa.accept_10_3_8_1_1_182 13 18 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 141 3 4 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 18 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 141 3 3 6 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 141
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 18 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 141 3 2 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 18 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 141
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 18 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 141 3 1 6 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 141 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 18 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 141 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 18 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 141)))))))))))))))))) (allB_succ 17 141
  (allA_succ_of_accept 16 17 141 (accept_3_4 16 17 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 141 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 17 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 17 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 141 (accept_3_4 13 17 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 141 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 141
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 17 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 141 (accept_3_4 10 17 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 17 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 141 (accept_3_4 7 17 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 141 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 17 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 141
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 141 (accept_3_4 4 17 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  141 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 17 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 17 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 141 (accept_3_4 1 17 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 141))))))))))))))))) (allB_succ 16 141 (allA_succ_of_accept 15 16 141
  (Polychromatic418967fa.accept_10_5_6_1_1_836 15 16 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 141 (accept_3_5 14 16 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 16 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 141 (accept_3_5 11 16 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 16 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 141
  (Polychromatic418967fa.accept_15_9_1_6_1_657 9 16 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 141 (accept_3_5 8 16 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  141 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 141 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 16 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 141 (accept_3_5 5 16 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 141 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 16 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 141 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  16 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 141 (accept_3_5 2 16 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 141)))))))))))))))) (allB_succ 15 141
  (allA_succ_of_accept 14 15 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 141 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 15 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 141 3 4 5 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 141
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 15 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 141 3 3 5 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 141 (Polychromatic418967fa.accept_24_8_15_21_1_7253 8 15 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 141
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 15 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 141 3 2 5 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 141 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 15 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 141 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 15 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 141 3 1 5 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 141 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 15 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 141))))))))))))))) (allB_succ 14 141 (allA_succ_of_accept 13 14 141
  (accept_3_4 13 14 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 141
  (Polychromatic418967fa.accept_9_3_5_6_1_253 12 14 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 141 (accept_3_4 10 14 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 141 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 14 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 141 (Polychromatic418967fa.accept_9_8_5_6_1_538 8
  14 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 141 (accept_3_4 7 14 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 141 (Polychromatic418967fa.accept_11_6_3_9_1_906 6
  14 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 141
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 14 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 141 (accept_3_4 4 14 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 141 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 14 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 141 (accept_3_4 1 14 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 141)))))))))))))) (allB_succ 13 141 (allA_succ_of_accept 12 13 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 141 (accept_3_5 11 13 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 141 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 13 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 13 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 141 (accept_3_5 8 13 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 141 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 13 141 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 141
  (Polychromatic418967fa.accept_19_6_13_8_1_4508 6 13 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 141 (accept_3_5 5 13 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  141 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 141 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 13 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 141 (accept_3_5 2 13 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 141 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 13 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 141))))))))))))) (allB_succ 12 141 (allA_succ_of_accept 11 12
  141 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 12 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 141 3 3 4 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 141 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 12 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 141
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 141 3 2 4 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 141 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 141 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 12 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 141 3 1 4 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 141
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 12 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 141 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 12 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 141)))))))))))) (allB_succ 11 141 (allA_succ_of_accept 10 11 141
  (accept_3_4 10 11 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 141
  (Polychromatic418967fa.accept_15_9_11_6_1_637 9 11 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 141 (accept_3_4 7 11 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 141 (Polychromatic418967fa.accept_7_5_4_1_1_412 5
  11 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 141 (accept_3_4 4 11 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 141 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 11
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 141 (accept_3_4 1 11 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  141))))))))))) (allB_succ 10 141 (allA_succ_of_accept 9 10 141 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 10 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 141 (accept_3_5 8 10 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 141
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 10 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 141 (accept_3_5 5 10 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  141 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 10 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 10 141 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 141 (accept_3_5 2 10 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 10 141 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 10 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 141)))))))))) (allB_succ 9 141 (allA_succ_of_accept 8 9 141
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 9 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 141 (Polychromatic418967fa.accept_13_7_9_11_1_705 7 9 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 141 3 2 3 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 141 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 9 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 141
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 9 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 141 3 1 3 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 141 (Polychromatic418967fa.accept_10_2_9_1_1_185 2 9 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 141 (Polychromatic418967fa.accept_13_1_9_11_1_703 1 9 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 141))))))))) (allB_succ 8 141
  (allA_succ_of_accept 7 8 141 (accept_3_4 7 8 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 141
  (Polychromatic418967fa.accept_12_6_8_9_1_553 6 8 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 141 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 141 (accept_3_4 4 8 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 141 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 8 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 141 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 8
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 141 (accept_3_4 1 8 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 141)))))))) (allB_succ 7 141 (allA_succ_of_accept 6 7 141
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 141 (accept_3_5 5 7 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 141
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 141 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 141 (accept_3_5 2 7 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 141 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 7 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 141))))))) (allB_succ 6 141 (allA_succ_of_accept 5 6 141
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 6 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 141 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 6 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 141 3 1 2 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 141 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 6 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 141
  (Polychromatic418967fa.accept_17_1_6_5_1_3502 1 6 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 141)))))) (allB_succ 5 141 (allA_succ_of_accept 4 5 141 (accept_3_4 4 5 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 141 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 5 141 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 141 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5
  141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 141 (accept_3_4 1 5 141
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 141))))) (allB_succ 4 141 (allA_succ_of_accept 3 4 141
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 4 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 141 (accept_3_5 2 4 141 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 141
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 141)))) (allB_succ 3 141 (allA_succ_of_accept 2 3 141 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 141
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 141
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 3 141 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 141))) (allB_succ 2 141 (allA_succ_of_accept 1 2 141 (accept_3_4 1 2 141 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 141)) (allB_two
  141)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


