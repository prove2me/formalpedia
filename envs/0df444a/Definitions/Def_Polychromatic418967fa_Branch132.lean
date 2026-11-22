-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch132
-- name    : Polychromatic418967fa_Branch132
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:14:32.862689+00:00
-- url     : https://prove2.me/theorems/d251bf8b-0cea-4675-9966-278a55714507
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

def Polychromatic418967fa.branch_132 : allB 132 132 :=
  allB_succ' 2 131 132 (Eq.refl Bool.true) (allA_succ_of_accept 1 131 132 (accept_3_4 1 131 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 132)) (allB_succ' 3 130 132 (Eq.refl Bool.true) (allA_succ_of_gcd 2 130 132 2 1 65
  66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 132
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 130 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 130 132))) (allB_succ' 4 129 132 (Eq.refl Bool.true) (allA_succ_of_gcd 3 129 132 3 1 43 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 129 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 129 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 129 132)))) (allB_succ' 5 128 132 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  128 132 4 1 32 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 128 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 128 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 128 132 2 1 64 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 128 132 (accept_3_4 1 128 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  132))))) (allB_succ' 6 127 132 (Eq.refl Bool.true) (allA_succ_of_accept 5 127 132 (accept_3_5 5 127 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 127 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 132
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 127 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 132 (accept_3_5 2 127 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 132 (Polychromatic418967fa.accept_19_1_13_18_1_6700 1 127 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 132)))))) (allB_succ' 7 126 132 (Eq.refl Bool.true) (allA_succ_of_gcd 6 126 132 6 1 21 22
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 132
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 126 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 126 132 2 2 63 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 126 132 3 1 42 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 126 132 2 1 63 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 126 132 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 126 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 126 132))))))) (allB_succ' 8 125 132 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 125 132 (accept_3_4 7 125 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 132 (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 125 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 125 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 132 (accept_3_4 4 125 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 125 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 132
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 125 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 132 (accept_3_4 1 125 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  132)))))))) (allB_succ' 9 124 132 (Eq.refl Bool.true) (allA_succ_of_gcd 8 124 132 4 2 31 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 132
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 124 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 124 132 2 3 62 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 124 132 (accept_3_5 5 124 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124
  132 4 1 31 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  124 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 124 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 124 132 2 1 62 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 124 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 124 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 132))))))))) (allB_succ' 10 123 132 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 123 132 3 3 41 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 123 132 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 123 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 123 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 132 3 2 41 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 132
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 123 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 132 (Polychromatic418967fa.accept_13_4_6_2_1_1437 4 123 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 132 3 1 41 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 123 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 132
  (Polychromatic418967fa.accept_10_1_3_2_1_220 1 123 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 123 132)))))))))) (allB_succ' 11 122 132 (Eq.refl Bool.true) (allA_succ_of_gcd 10 122 132 2 5 61 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 122 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 132 2 4 61 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 132 (accept_3_4 7 122 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  132 2 3 61 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 132 (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 122 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 132 2 2 61 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 122 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 122 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 132 2 1 61 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 132 (accept_3_4 1 122 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 122 132))))))))))) (allB_succ' 12 121 132 (Eq.refl Bool.true) (allA_succ_of_gcd 11 121
  132 11 1 11 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10
  121 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 121 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 132 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 121 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 132 (accept_3_5 8 121 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 121 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 132
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 121 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 132 (accept_3_5 5 121 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 121 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 121 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 132 (accept_3_5 2 121 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 121 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 132)))))))))))) (allB_succ' 13 120 132 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 120 132 12 1 10 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 120 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 120 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 132 2 5 60 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 120 132 3 3 40 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 120 132 4 2 30 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 120 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 132 6 1 20 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 120 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 132 4 1 30 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 120 132 3 1 40 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 120 132 2 1 60 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 120 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120 132))))))))))))) (allB_succ' 14 119 132
  (Eq.refl Bool.true) (allA_succ_of_accept 13 119 132 (accept_3_4 13 119 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 119 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 119 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 119 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 132 (accept_3_4 10 119 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 132 (Polychromatic418967fa.accept_15_9_14_12_1_913
  9 119 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 132
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 119 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 132 (accept_3_4 7 119 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 132 (Polychromatic418967fa.accept_19_6_5_18_1_5228 6 119 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 132 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 119 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 132 (accept_3_4 4 119 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 119 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 132
  (Polychromatic418967fa.accept_15_2_14_12_1_2453 2 119 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 132 (accept_3_4 1 119 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  132)))))))))))))) (allB_succ' 15 118 132 (Eq.refl Bool.true) (allA_succ_of_gcd 14 118 132 2 7 59 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 118 132
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 118 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 118 132 2 6 59 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 118 132 (accept_3_5 11 118 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  118 132 2 5 59 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 118 132 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 118 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 118 132 2 4 59 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 118 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 118 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 132 2 3 59 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 132 (accept_3_5 5 118 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118 132 2 2 59 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 118 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 118 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 132 2 1 59 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 132
  (Polychromatic418967fa.accept_15_1_13_12_1_347 1 118 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 118 132))))))))))))))) (allB_succ' 16 117 132 (Eq.refl Bool.true) (allA_succ_of_gcd 15 117 132 3 5 39 44
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 132
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 117 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 132 (Polychromatic418967fa.accept_14_13_5_6_1_2747 13 117 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 132 3 4 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 11
  117 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 132
  (Polychromatic418967fa.accept_21_10_12_6_1_5124 10 117 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 117 132 3 3 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 117 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 117 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 132 (Polychromatic418967fa.accept_18_7_9_6_1_4023
  7 117 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 132 3 2 39 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 132
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 117 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 117 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 132 3 1 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 132 (Polychromatic418967fa.accept_17_2_15_13_1_3034 2 117
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 132
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 117 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 117 132)))))))))))))))) (allB_succ' 17 116 132 (Eq.refl Bool.true) (allA_succ_of_gcd 16 116 132 4 4 29 33
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 132
  (Polychromatic418967fa.accept_19_15_2_18_1_6699 15 116 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 116 132 2 7 58 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 116 132 (accept_3_4 13 116 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 116 132 4 3 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 116 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 116 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 116 132 2 5 58 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 9
  116 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 132 4 2 29 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 132 (accept_3_4 7
  116 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 132 2 3 58 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 132
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 116 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 116 132 4 1 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 116 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 116 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 132 2 1 58 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 132 (accept_3_4 1 116 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 116 132))))))))))))))))) (allB_succ' 18 115 132 (Eq.refl Bool.true) (allA_succ_of_accept 17 115
  132 (accept_3_5 17 115 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 16 115 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 115 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 115 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 132 (accept_3_5 14 115 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 115 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 115 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 12
  115 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 132 (accept_3_5 11
  115 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 132
  (Polychromatic418967fa.accept_9_1_7_6_1_75 10 115 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 115 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 115 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 132 (accept_3_5 8 115 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 115 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 115 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 132
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 6 115 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 132 (accept_3_5 5 115 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 115 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 115 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 132 (accept_3_5 2 115 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 115 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 132)))))))))))))))))) (allB_succ' 19 114 132
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 114 132 6 3 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 114 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 114 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 132 2 8 57 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 132 3 5 38 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 132 2 7 57 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 132
  (Polychromatic418967fa.accept_21_13_9_6_1_1190 13 114 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 132 6 2 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 114 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 114 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 132 2 5 57 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 132 3 3 38 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 132 2 4 57 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 132 (Polychromatic418967fa.accept_10_7_4_2_1_903 7
  114 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 132 6 1 19 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 132
  (Polychromatic418967fa.accept_13_5_10_2_1_856 5 114 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 114 132 2 2 57 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 114 132 3 1 38 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 114 132 2 1 57 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 114 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 114 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 114 132))))))))))))))))))) (allB_succ' 20 113 132 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 113 132 (accept_3_4 19 113 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 132 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 113 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 132 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 113 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 132 (accept_3_4 16 113 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 132 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 113 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 132
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 14 113 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 132 (accept_3_4 13 113 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 113 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 113 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 132 (accept_3_4 10 113 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 113 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 132
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 113 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 132 (accept_3_4 7 113 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 132 (Polychromatic418967fa.accept_13_6_9_2_1_838 6 113 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 113 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 132 (accept_3_4 4 113 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 113 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 132
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 113 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 132 (accept_3_4 1 113 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  132)))))))))))))))))))) (allB_succ' 21 112 132 (Eq.refl Bool.true) (allA_succ_of_gcd 20 112 132 4 5 28 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 132
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 112 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 132 2 9 56 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 132 (accept_3_5 17 112 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 132 4 4 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 132 (Polychromatic418967fa.accept_18_15_4_6_1_1763 15 112 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 132 2 7 56 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 132 (Polychromatic418967fa.accept_19_13_17_18_1_6638 13 112 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 132 4 3 28 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 132 (accept_3_5 11
  112 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 132 2 5 56 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 132
  (Polychromatic418967fa.accept_17_9_10_13_1_6698 9 112 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 132 4 2 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 112 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 132 2 3 56 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 132 (accept_3_5 5 112 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 132 4 1 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 112 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 132 2 1 56 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 112
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 132))))))))))))))))))))) (allB_succ' 22
  111 132 (Eq.refl Bool.true) (allA_succ_of_gcd 21 111 132 3 7 37 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 111 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 132
  (Polychromatic418967fa.accept_8_3_7_4_1_42 19 111 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 111 132 3 6 37 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 111 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 111 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 111 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 132 3 5 37 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 132
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 111 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 111 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 132 3 4 37 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 11
  111 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 132
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 111 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 111 132 3 3 37 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 111 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 111 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 111 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 132 3 2 37 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 132
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 111 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 111 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 132 3 1 37 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 111 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 132
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 111 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111 132)))))))))))))))))))))) (allB_succ' 23 110 132 (Eq.refl Bool.true) (allA_succ_of_gcd 22 110 132 22 1 5
  6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 132
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 110 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 132 2 10 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 132 (accept_3_4 19 110 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 132 2 9 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 110 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 132 2 8 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  110 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 132 2 7 55 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 132 (accept_3_4 13
  110 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 132 2 6 55 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 110 132 11 1 10 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 110 132 2 5 55 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 132
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 110 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 132 2 4 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 132 (accept_3_4 7 110 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  132 2 3 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 132 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 110 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 132 2 2 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 110 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 110 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 132 2 1 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 132 (accept_3_4 1 110 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110 132))))))))))))))))))))))) (allB_succ' 24 109 132 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 109 132 (accept_3_5 23 109 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 109 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 109 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 132 (accept_3_5 20 109 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 109 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 132
  (Polychromatic418967fa.accept_21_18_4_6_1_6697 18 109 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 132 (accept_3_5 17 109 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 109 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 132 (Polychromatic418967fa.accept_19_15_14_18_1_6696 15 109 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 132 (accept_3_5 14 109 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 109 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 132
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 109 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 132 (accept_3_5 11 109 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 109 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 109 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 132 (accept_3_5 8 109 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 109 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 132
  (Polychromatic418967fa.accept_16_6_13_4_1_643 6 109 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 132 (accept_3_5 5 109 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 109 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 109 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 132 (accept_3_5 2 109 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 109 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109 132)))))))))))))))))))))))) (allB_succ' 25 108 132
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 108 132 12 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 108 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 108 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 132 2 11 54 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 132 3 7 36 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 132 4 5 27 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 132
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 19 108 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 132 6 3 18 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 132 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 108 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 132 4 4 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 132 3 5 36 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 132 2 7 54 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 132
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 108 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 108 132 12 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 108 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 108 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 132 2 5 54 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 108 132 3 3 36 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 108 132 4 2 27 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 132
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 108 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 108 132 6 1 18 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 108 132 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 108 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 132 4 1 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 108 132 3 1 36 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 108 132 2 1 54 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 132 (Polychromatic418967fa.accept_16_1_12_4_1_695 1 108 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108 132))))))))))))))))))))))))) (allB_succ' 26
  107 132 (Eq.refl Bool.true) (allA_succ_of_accept 25 107 132 (accept_3_4 25 107 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 107 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 107 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 132 (Polychromatic418967fa.accept_8_7_3_4_1_404
  23 107 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 132 (accept_3_4 22
  107 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 132
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 107 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 107 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 107 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 132 (accept_3_4 19 107 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 107 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 107 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  107 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 132 (accept_3_4 16
  107 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 107 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 107 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 107 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 132 (accept_3_4 13 107 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 107 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 107 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 132 (Polychromatic418967fa.accept_7_4_2_6_1_337
  11 107 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 132 (accept_3_4 10
  107 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 132
  (Polychromatic418967fa.accept_10_9_7_2_1_887 9 107 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 107 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 107 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 132 (accept_3_4 7 107 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 107 132 (Polychromatic418967fa.accept_15_6_2_12_1_885 6 107 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 5
  107 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 132 (accept_3_4 4 107
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 132 (Polychromatic418967fa.accept_7_3_2_6_1_56
  3 107 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 132
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 107 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 132 (accept_3_4 1 107 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  132)))))))))))))))))))))))))) (allB_succ' 27 106 132 (Eq.refl Bool.true) (allA_succ_of_gcd 26 106 132 2 13 53 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 132
  (Polychromatic418967fa.accept_17_8_4_13_1_3014 25 106 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 132 2 12 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 132 (accept_3_5 23 106 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 132 2 11 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 106 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 132 2 10 53 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 132
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 106 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 132 2 9 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 132 (accept_3_5 17 106 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 132 2 8 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 132 (Polychromatic418967fa.accept_18_15_16_6_1_1751 15 106 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 132 2 7 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 106 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 132 2 6 53 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 132 (accept_3_5 11 106 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 132 2 5 53 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 132
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 106 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 132 2 4 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 132 (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 106 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 132 2 3 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 132 (accept_3_5 5 106 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 132 2 2 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 106 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 132 2 1 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 1
  106 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 132)))))))))))))))))))))))))))
  (allB_succ' 28 105 132 (Eq.refl Bool.true) (allA_succ_of_gcd 27 105 132 3 9 35 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 105 132
  (Polychromatic418967fa.accept_19_7_10_18_1_6695 26 105 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 105 132 (Polychromatic418967fa.accept_13_12_1_2_1_845 25 105 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 105 132 3 8 35 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 132
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 105 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 132 (Polychromatic418967fa.accept_13_9_1_2_1_2952 22 105 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 132 3 7 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 132 (Polychromatic418967fa.accept_25_20_5_7_1_6694
  20 105 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 132
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 105 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 105 132 3 6 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 105 132 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 105 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 132 (Polychromatic418967fa.accept_13_3_1_2_1_2960 16 105
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 132 3 5 35 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 132
  (Polychromatic418967fa.accept_16_14_9_4_1_6693 14 105 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 105 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 132 3 4 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 132 (Polychromatic418967fa.accept_16_11_9_4_1_5438
  11 105 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 132
  (Polychromatic418967fa.accept_17_10_3_13_1_6639 10 105 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 105 132 3 3 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 105 132 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 105 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 132 (Polychromatic418967fa.accept_10_7_5_2_1_880 7
  105 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 132 3 2 35 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 105 132
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 105 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 132 (Polychromatic418967fa.accept_17_4_3_13_1_6692 4 105 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 132 3 1 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 132 (Polychromatic418967fa.accept_19_2_10_18_1_6691 2 105
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 132
  (Polychromatic418967fa.accept_14_1_7_6_1_3604 1 105 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 105 132)))))))))))))))))))))))))))) (allB_succ' 29 104 132 (Eq.refl Bool.true) (allA_succ_of_gcd 28 104 132
  4 7 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104
  132 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 104 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 104 132 2 13 52 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 104 132 (accept_3_4 25 104 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 132 4 6 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 104 132 (Polychromatic418967fa.accept_16_7_8_4_1_689 23 104 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 132 2 11 52 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 21
  104 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 104 132 4 5 26 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 104 132 (accept_3_4 19
  104 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 104 132 2 9 52 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 104 132
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 104 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 104 132 4 4 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 104 132 (Polychromatic418967fa.accept_16_15_8_4_1_1355 15 104 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 132 2 7 52 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 132 (accept_3_4 13 104 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 132 4 3 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 104 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 132 2 5 52 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 132
  (Polychromatic418967fa.accept_15_9_14_12_1_913 9 104 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 132 4 2 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 132 (accept_3_4 7 104 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  132 2 3 52 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 132 (Polychromatic418967fa.accept_16_5_8_4_1_5418 5 104 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 132 4 1 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 104 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 104 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 132 2 1 52 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 132 (accept_3_4 1 104 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 132))))))))))))))))))))))))))))) (allB_succ' 30 103 132 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 103 132 (accept_3_5 29 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 103 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 132 (accept_3_5 26 103 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 103 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 132
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 24 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 132 (accept_3_5 23 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 103 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 132 (accept_3_5 20 103 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 103 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 132 (accept_3_5 17 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 103 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 132 (accept_3_5 14 103 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 132 (Polychromatic418967fa.accept_14_13_5_6_1_2747 13 103 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 132
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 132 (accept_3_5 11 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 132 (Polychromatic418967fa.accept_18_9_13_6_1_877 9 103 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 132 (accept_3_5 8 103 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 103 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 132
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 132 (accept_3_5 5 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 103 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 103 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 132 (accept_3_5 2 103 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 103 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 132)))))))))))))))))))))))))))))) (allB_succ' 31 102
  132 (Eq.refl Bool.true) (allA_succ_of_gcd 30 102 132 6 5 17 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 102 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 102 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 132 2 14 51 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 102 132 3 9 34 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 102 132 2 13 51 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 102 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 132 6 4 17 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 102 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 102 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 132 2 11 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 132 3 7 34 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 132 2 10 51 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 132
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 102 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 132 6 3 17 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 102 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 132 2 8 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 132 3 5 34 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 132 2 7 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 13
  102 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 132 6 2 17 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 102 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 132 2 5 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 102 132 3 3 34 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 102 132 2 4 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 102 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 132 6 1 17 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 102 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 132 2 2 51 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 102 132 3 1 34 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 102 132 2 1 51 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 132
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 102 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102 132))))))))))))))))))))))))))))))) (allB_succ' 32 101 132 (Eq.refl Bool.true) (allA_succ_of_accept 31
  101 132 (accept_3_4 31 101 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 101 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 101 132 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 101 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 132 (accept_3_4 28 101 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 101 132 (Polychromatic418967fa.accept_24_3_5_12_1_6657 27 101 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 132
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 101 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 132 (accept_3_4 25 101 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 132 (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 101 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 101 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 132 (accept_3_4 22 101 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 101 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 132
  (Polychromatic418967fa.accept_17_3_16_13_1_6635 20 101 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 101 132 (accept_3_4 19 101 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 101 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 101 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 101 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 132 (accept_3_4 16 101 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 132
  (Polychromatic418967fa.accept_16_15_5_4_1_6678 15 101 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 101 132 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 101 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 132 (accept_3_4 13 101 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 101 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 101 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 132 (Polychromatic418967fa.accept_7_4_3_6_1_340
  11 101 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 132 (accept_3_4 10
  101 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 101 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 101 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 101 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 132 (accept_3_4 7 101 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 101 132 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 101 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 132 (Polychromatic418967fa.accept_9_5_2_6_1_265 5
  101 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 132 (accept_3_4 4 101
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 132
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 101 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 101 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 101 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 132 (accept_3_4 1 101 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 101 132)))))))))))))))))))))))))))))))) (allB_succ' 33 100 132 (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 100 132 4 8 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 100 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 100 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 132 2 15 50 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 132 (accept_3_5 29 100 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 132 4 7 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 132 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 100
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 132 2 13 50 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 132
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 100 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 100 132 4 6 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 100 132 (accept_3_5 23 100 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  100 132 2 11 50 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 100 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 100 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 132 4 5 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 132 (Polychromatic418967fa.accept_13_6_9_2_1_838
  19 100 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 132 2 9 50 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 132
  (accept_3_5 17 100 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 132 4 4 25 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 100 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 100 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 100 132 2 7 50 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 100 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 100 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 132 4 3 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 132 (accept_3_5 11 100 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 132 2 5 50 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 132 (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 100
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 132 4 2 25 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 132
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 100 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 100 132 2 3 50 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 100 132 (accept_3_5 5 100 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100
  132 4 1 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  100 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 100 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 100 132 2 1 50 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 100 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 100 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 132))))))))))))))))))))))))))))))))) (allB_succ' 34 99 132
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 99 132 33 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 99 132 (Polychromatic418967fa.accept_13_6_8_2_1_1484 32 99 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 132
  (Polychromatic418967fa.accept_8_7_3_4_1_404 31 99 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 99 132 3 10 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 99 132 (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 99 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 132 (Polychromatic418967fa.accept_16_12_3_4_1_4317 28 99
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 132 3 9 33 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 132
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 99 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 132 (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 99 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 99 132 3 8 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 99 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 99 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 99 132 11 2 9 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 99 132 3 7 33 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 132
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 99 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 99 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 132 3 6 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 132 (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 99 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 132
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 99 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 132 3 5 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 132 (Polychromatic418967fa.accept_15_14_9_12_1_2498 14 99 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 132 (Polychromatic418967fa.accept_18_13_9_6_1_4024 13 99
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 132 3 4 33 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 99 132 11 1 9 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 99 132
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 10 99 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 99 132 3 3 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 99 132 (Polychromatic418967fa.accept_16_8_3_4_1_3233 8 99 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 99 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 132 3 2 33 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 132
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 99 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 132 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 99 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 132 3 1 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 99 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 132
  (Polychromatic418967fa.accept_10_1_9_2_1_45 1 99 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 132)))))))))))))))))))))))))))))))))) (allB_succ' 35 98 132 (Eq.refl Bool.true) (allA_succ_of_gcd 34 98
  132 2 17 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  98 132 (Polychromatic418967fa.accept_15_3_8_12_1_900 33 98 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 98 132 2 16 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 98 132 (accept_3_4 31 98 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 132 2 15 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 98 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 98 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 132 2 14 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 132 (Polychromatic418967fa.accept_18_9_8_6_1_4021
  27 98 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 98 132 2 13 49 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 98 132 (accept_3_4 25
  98 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98 132 2 12 49 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 98 132
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 98 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 98 132 2 11 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 98 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 98 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 132 2 10 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 132 (accept_3_4 19 98 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 132 2 9 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 98 132 (Polychromatic418967fa.accept_36_17_26_24_1_6690 17 98 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 132 2 8 49 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 132
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 98 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 132 2 7 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 132 (accept_3_4 13 98 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  132 2 6 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 98 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 132 2 5 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 132 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 98 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 132 2 4 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 132 (accept_3_4 7 98 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 132 2 3 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 98 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 132 2 2 49 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 132
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 98 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 132 2 1 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 132 (accept_3_4 1 98 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  132))))))))))))))))))))))))))))))))))) (allB_succ' 36 97 132 (Eq.refl Bool.true) (allA_succ_of_accept 35 97 132
  (accept_3_5 35 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 132
  (Polychromatic418967fa.accept_10_4_7_2_1_211 34 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 97 132 (Polychromatic418967fa.accept_14_5_13_6_1_3574 33 97 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 132 (accept_3_5 32 97 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 97 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 97 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 30
  97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 132 (accept_3_5 29 97
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 132 (Polychromatic418967fa.accept_9_1_7_6_1_75
  28 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 132
  (Polychromatic418967fa.accept_13_1_6_2_1_377 27 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 132 (accept_3_5 26 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 132 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 132 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 97 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 132 (accept_3_5 23 97 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 97 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 132
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 132 (accept_3_5 20 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 132 (Polychromatic418967fa.accept_15_3_7_12_1_372 18 97 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 132 (accept_3_5 17 97 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 132 (Polychromatic418967fa.accept_17_16_12_13_1_3070 16 97 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 132
  (Polychromatic418967fa.accept_10_5_7_2_1_516 15 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 132 (accept_3_5 14 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 97 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 132 (accept_3_5 11 97 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 97 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 132
  (Polychromatic418967fa.accept_10_9_7_2_1_887 9 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 132 (accept_3_5 8 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  132 (Polychromatic418967fa.accept_14_7_13_6_1_1177 7 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 132 (Polychromatic418967fa.accept_15_6_7_12_1_869 6 97 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 132 (accept_3_5 5 97 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 97 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 132
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 132 (accept_3_5 2 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  132 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 97 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 132)))))))))))))))))))))))))))))))))))) (allB_succ' 37 96 132 (Eq.refl Bool.true) (allA_succ_of_gcd 36 96
  132 12 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  96 132 (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 96 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 96 132 2 17 48 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 96 132 3 11 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 96 132 4 8 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 96 132 (Polychromatic418967fa.accept_10_1_6_2_1_867 31 96 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 132 6 5 16 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 132
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 96 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 96 132 4 7 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 96 132 3 9 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 96 132 2 13 48 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 96 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 96 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 132 12 2 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 132 (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 96 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 132 2 11 48 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 96 132 3 7 32 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 96 132 4 5 24 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 132
  (Polychromatic418967fa.accept_21_19_12_6_1_6689 19 96 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 132 6 3 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 132 (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 96 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 132 4 4 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 96 132 3 5 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 96 132 2 7 48 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 132 (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 96
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 132 12 1 8 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 96 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 96 132 2 5 48 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 96 132 3 3 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 96 132 4 2 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 132 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 96 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 132 6 1 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 132 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 96 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 132 4 1 24 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 96 132 3 1 32 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 96 132 2 1 48 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 132
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 96 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 132))))))))))))))))))))))))))))))))))))) (allB_succ' 38 95 132 (Eq.refl Bool.true) (allA_succ_of_accept
  37 95 132 (accept_3_4 37 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 132
  (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 95 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 95 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 132 (accept_3_4 34 95 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 95 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 95 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 132 (Polychromatic418967fa.accept_13_6_4_2_1_1433
  32 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 132 (accept_3_4 31
  95 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 95 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 95 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 132 (accept_3_4 28 95 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 95 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 95 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 26
  95 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 132 (accept_3_4 25 95
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 132
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 95 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 95 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 132 (accept_3_4 22 95 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 95 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 95 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 20
  95 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 132 (accept_3_4 19 95
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 132
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 95 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 132 (accept_3_4 16 95 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 95 132 (Polychromatic418967fa.accept_18_15_5_6_1_5293 15 95 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 132
  (Polychromatic418967fa.accept_16_14_15_4_1_3268 14 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 132 (accept_3_4 13 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 95 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 132 (accept_3_4 10 95 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 95 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 132
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 132 (accept_3_4 7 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  132 (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 95 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 95 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 132 (accept_3_4 4 95 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 95 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 132 (accept_3_4 1 95 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  132)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 94 132 (Eq.refl Bool.true) (allA_succ_of_gcd 38 94 132 2 19
  47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 94 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 132 2 18 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 94 132 (accept_3_5 35 94 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94
  132 2 17 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  94 132 (Polychromatic418967fa.accept_16_1_14_4_1_3220 33 94 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 94 132 2 16 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 94 132 (Polychromatic418967fa.accept_13_5_3_2_1_1499 31 94 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 94 132 2 15 47 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 94 132 (accept_3_5 29 94 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94 132 2 14 47 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 94 132
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 94 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 94 132 2 13 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 94 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 94 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 132 2 12 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 132 (accept_3_5 23 94 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 132 2 11 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 94 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 132 2 10 47 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 132
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 94 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 132 2 9 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 132 (accept_3_5 17 94 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  132 2 8 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 132 (Polychromatic418967fa.accept_16_15_14_4_1_6649 15 94 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 132 2 7 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 94 132 (Polychromatic418967fa.accept_25_13_19_7_1_6688 13 94 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 132 2 6 47 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 132 (accept_3_5 11 94 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 132 2 5 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 94 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 94 132 2 4 47 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 94 132
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 94 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 94 132 2 3 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 94 132 (accept_3_5 5 94 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 132
  2 2 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 94
  132 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 94 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 94 132 2 1 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 94 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 94 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 94 132))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 93 132 (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 93 132 3 13 31 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 93 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 93 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  93 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 132 3 12 31 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 132
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 93 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 93 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 132 3 11 31 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 32
  93 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 93 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 93 132 3 10 31 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 93 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 93 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 93 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 132 3 9 31 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 132
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 93 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 93 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 132 3 8 31 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 93 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 93 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 132 3 7 31 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 93 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 93 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 132 3 6 31 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 93 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 93 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 132 3 5 31 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 93 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 132
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 93 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 132 3 4 31 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 93 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 93 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 132 3 3 31 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 93 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 93 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 132 3 2 31 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 93 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 132
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 93 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 132 3 1 31 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 93 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 93 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 132))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 92 132 (Eq.refl Bool.true) (allA_succ_of_gcd 40 92 132 4 10 23 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 132
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 92 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 132 2 19 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 92 132 (accept_3_4 37 92 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92
  132 4 9 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  92 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 92 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 92 132 2 17 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 92 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 92 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 132 4 8 23 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 132 (accept_3_4 31 92 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 132 2 15 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 132 (Polychromatic418967fa.accept_13_3_1_2_1_2960
  29 92 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 92 132 4 7 23 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 132
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 27 92 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 92 132 2 13 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 92 132 (accept_3_4 25 92 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92
  132 4 6 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  92 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 92 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 92 132 2 11 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 92 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 92 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 132 4 5 23 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 132 (accept_3_4 19 92 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 132 2 9 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 92 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 92 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 132 4 4 23 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 132
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 92 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 92 132 2 7 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 92 132 (accept_3_4 13 92 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92
  132 4 3 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  92 132 (Polychromatic418967fa.accept_16_11_12_4_1_3195 11 92 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 92 132 2 5 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 92 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 92 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 132 4 2 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 132 (accept_3_4 7 92 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 132 2 3 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 92 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 92 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 132 4 1 23 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 132
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 92 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 92 132 2 1 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 92 132 (accept_3_4 1 92 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  132))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 91 132 (Eq.refl Bool.true) (allA_succ_of_accept 41 91 132
  (accept_3_5 41 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 132
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 91 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 91 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 132 (accept_3_5 38 91 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 91 132 (Polychromatic418967fa.accept_21_16_7_6_1_6687 37 91 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 132
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 132 (accept_3_5 35 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 132 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 91 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 132 (accept_3_5 32 91 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 91 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 132 (accept_3_5 29 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 132 (Polychromatic418967fa.accept_15_13_1_12_1_1638 28 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 132 (Polychromatic418967fa.accept_14_13_7_6_1_3525 27 91 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 132 (accept_3_5 26 91 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 91 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 132
  (Polychromatic418967fa.accept_16_8_11_4_1_3290 24 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 132 (accept_3_5 23 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 91 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 132 (accept_3_5 20 91 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 132 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 91 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 132
  (Polychromatic418967fa.accept_21_18_7_6_1_3609 18 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 132 (accept_3_5 17 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 91 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 132 (accept_3_5 14 91 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 91 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 132 (accept_3_5 11 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 132 (Polychromatic418967fa.accept_25_10_16_7_1_6686 10 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 132 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 91 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 132 (accept_3_5 8 91 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 91 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 132
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 132 (accept_3_5 5 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  132 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 91 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 132 (accept_3_5 2 91 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 132 (Polychromatic418967fa.accept_14_1_7_6_1_3604 1 91 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 132)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 90
  132 (Eq.refl Bool.true) (allA_succ_of_gcd 42 90 132 6 7 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 132 (Polychromatic418967fa.accept_19_3_14_18_1_6685 41 90
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 132 2 20 45 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 90 132 3 13 30 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 90 132 2 19 45 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 132
  (Polychromatic418967fa.accept_24_13_18_12_1_3288 37 90 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 90 132 6 6 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 90 132 (Polychromatic418967fa.accept_19_16_14_18_1_6684 35 90 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 132 2 17 45 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 90 132 3 11 30 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 90 132 2 16 45 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 132
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 31 90 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 132 6 5 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 90 132 (Polychromatic418967fa.accept_13_3_12_2_1_385 29 90 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 132 2 14 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 90 132 3 9 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 90 132 2 13 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 132 (Polychromatic418967fa.accept_17_8_5_13_1_4158
  25 90 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 132 6 4 15 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 132
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 90 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 132 2 11 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 90 132 3 7 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 90 132 2 10 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 132 (Polychromatic418967fa.accept_13_6_12_2_1_4707 19 90 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 132 6 3 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 132 (Polychromatic418967fa.accept_13_4_12_2_1_1459 17 90 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 132 2 8 45 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 132 3 5 30 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 132 2 7 45 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 132
  (Polychromatic418967fa.accept_19_13_14_18_1_6683 13 90 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 90 132 6 2 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 90 132 (Polychromatic418967fa.accept_23_11_21_17_1_6682 11 90 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 132 2 5 45 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 132 3 3 30 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 90 132 2 4 45 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 132
  (Polychromatic418967fa.accept_19_7_14_18_1_6654 7 90 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 132 6 1 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 90 132 (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 90 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 132 2 2 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 90 132 3 1 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 90 132 2 1 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 132 (Polychromatic418967fa.accept_13_1_12_2_1_384 1 90 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  132))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 89 132 (Eq.refl Bool.true) (allA_succ_of_accept 43 89
  132 (accept_3_4 43 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 132
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 42 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 89 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 89 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 132 (accept_3_4 40 89 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 89 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 89 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 132 (accept_3_4 37 89
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 132 (Polychromatic418967fa.accept_7_1_5_6_1_59
  36 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 132
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 132 (accept_3_4 34 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 132 (Polychromatic418967fa.accept_18_15_17_6_1_4043 33 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 89 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 132 (accept_3_4 31 89 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 89 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 132
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 132 (accept_3_4 28 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 132 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 132 (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 89 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 132 (accept_3_4 25 89 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 132 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 89
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 132
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 132 (accept_3_4 22 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 89 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 132 (accept_3_4 19 89 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 89 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 132
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 132 (accept_3_4 16 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 89 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 132 (accept_3_4 13 89 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 89 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 132 (accept_3_4 10 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 132 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 89 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 132 (accept_3_4 7 89 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 132 (Polychromatic418967fa.accept_24_6_17_12_1_6681 6 89 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 132
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 132 (accept_3_4 4 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  132 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 89 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 89 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 132 (accept_3_4 1 89 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 132)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 88 132 (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 88 132 44 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 88 132 (Polychromatic418967fa.accept_16_11_8_4_1_2234 43 88 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 132 2 21 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 132 (accept_3_5 41 88 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 132 4 10 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 88 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 132 2 19 44 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 88 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 132 4 9 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 132 (accept_3_5 35 88 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  132 2 17 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 88
  132 11 3 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 88
  132 4 8 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31
  88 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 88 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 88 132 2 15 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 88 132 (accept_3_5 29 88 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 88 132 4 7 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 88 132 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 88 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 132 2 13 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 132 (Polychromatic418967fa.accept_10_5_8_2_1_517 25
  88 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 132 4 6 22 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 132 (accept_3_5 23
  88 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 132 22 1 4 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 132
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 88 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 88 132 4 5 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 88 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 88 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 132 2 9 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 132 (accept_3_5 17 88 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 88 132 4 4 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 88 132 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 88 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 132 2 7 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 13
  88 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 132 4 3 22 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 88 132 11 1 8 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 88 132 2 5 44 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 88 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 88 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 88 132 4 2 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 88 132 (Polychromatic418967fa.accept_16_7_8_4_1_689 7 88 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 132 2 3 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 132 (accept_3_5 5 88 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 88 132 4 1 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 88 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 88 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 132 2 1 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 88
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  132))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 87 132 (Eq.refl Bool.true) (allA_succ_of_gcd 45 87 132
  3 15 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87
  132 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 87 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 87 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 87 132 3 14 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 87 132 (Polychromatic418967fa.accept_17_7_2_13_1_5397
  41 87 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 132
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 40 87 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 87 132 3 13 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 87 132 (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 87 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 87 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 132 3 12 29 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 132
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 87 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 132 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 87 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 87 132 3 11 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 87 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 32
  87 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 132
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 87 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 87 132 3 10 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 87 132 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 87 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 132 (Polychromatic418967fa.accept_16_12_7_4_1_687 28 87 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 132 3 9 29 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 132
  (Polychromatic418967fa.accept_19_7_11_18_1_6680 26 87 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 87 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 132 3 8 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 87 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 132
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 22 87 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 87 132 3 7 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 87 132 (Polychromatic418967fa.accept_13_7_9_2_1_2167 20 87 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 87 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 132 3 6 29 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 132
  (Polychromatic418967fa.accept_18_17_15_6_1_1797 17 87 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 87 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 132 3 5 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 132 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 87 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 132
  (Polychromatic418967fa.accept_16_13_7_4_1_3248 13 87 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 87 132 3 4 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 87 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 132 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 87
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 132 3 3 29 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 132
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 8 87 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 132 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 87 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 132 3 2 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 132 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 87 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 132
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 87 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 132 3 1 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 87 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 132 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 87 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  132)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 86 132 (Eq.refl Bool.true) (allA_succ_of_gcd 46 86
  132 2 23 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  86 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 86 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 86 132 2 22 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 86 132 (accept_3_4 43 86 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 132 2 21 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 86 132 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 86 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 132 2 20 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 39
  86 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 132 2 19 43 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 132 (accept_3_4 37
  86 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 132 2 18 43 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 132
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 86 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 86 132 2 17 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 86 132 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 86 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 86 132 2 16 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 86 132 (accept_3_4 31 86 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86 132 2 15 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 86 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 86 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 132 2 14 43 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 132
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 86 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 132 2 13 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 86 132 (accept_3_4 25 86 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86
  132 2 12 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  86 132 (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 86 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 86 132 2 11 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 86 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 86 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 132 2 10 43 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 132 (accept_3_4 19 86 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 132 2 9 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 86 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  86 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 132 2 8 43 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 86 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 132 2 7 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 132 (accept_3_4 13 86 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  132 2 6 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 86 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 132 2 5 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 132 (Polychromatic418967fa.accept_18_9_14_6_1_1790 9 86 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 132 2 4 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 132 (accept_3_4 7 86 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 132 2 3 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 132 (Polychromatic418967fa.accept_16_5_6_4_1_3211 5 86 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 132 2 2 43 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 86 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 132 2 1 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 132 (accept_3_4 1 86 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  132))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 85 132 (Eq.refl Bool.true) (allA_succ_of_accept 47
  85 132 (accept_3_5 47 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 132
  (Polychromatic418967fa.accept_9_1_4_6_1_5 46 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 85 132 (Polychromatic418967fa.accept_18_9_13_6_1_877 45 85 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 132 (accept_3_5 44 85 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 85 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 85 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 132
  (Polychromatic418967fa.accept_24_18_13_12_1_6679 42 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 85 132 (accept_3_5 41 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 85 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 85 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 85 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 132 (accept_3_5 38 85 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 37
  85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 132
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 132 (accept_3_5 35 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 85 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 132 (accept_3_5 32 85 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 132 (Polychromatic418967fa.accept_13_5_7_2_1_852 31 85 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 132
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 132 (accept_3_5 29 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 132 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 85 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 132 (accept_3_5 26 85 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 85 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 132
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 132 (accept_3_5 23 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 132 (Polychromatic418967fa.accept_13_9_7_2_1_3869 22 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 85 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 132 (accept_3_5 20 85 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 85 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 132
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 132 (accept_3_5 17 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 132 (Polychromatic418967fa.accept_16_15_5_4_1_6678 15 85 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 132 (accept_3_5 14 85 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 132 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 85 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 132
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 132 (accept_3_5 11 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 85 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 132 (accept_3_5 8 85 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 85 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 132
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 6 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 132 (accept_3_5 5 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  132 (Polychromatic418967fa.accept_24_4_13_12_1_6677 4 85 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 85 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 132 (accept_3_5 2 85 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 85 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 132))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 84 132 (Eq.refl Bool.true) (allA_succ_of_gcd 48 84 132 12 4 7 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 84 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 132 2 23 42 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 84 132 3 15 28 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 84 132 4 11 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 84 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 84 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 132 6 7 14 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 84 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 132 4 10 21 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 84 132 3 13 28 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 84 132 2 19 42 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 132
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 84 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 132 12 3 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 84 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 132 2 17 42 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 84 132 3 11 28 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 84 132 4 8 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 31
  84 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 132 6 5 14 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 84 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 132 4 7 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 84 132 3 9 28 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 84 132 2 13 42 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 84 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 84 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 132 12 2 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 84 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 132 2 11 42 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84 132 3 7 28 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84 132 4 5 21 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 132
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 84 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 132 6 3 14 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 84 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 132 4 4 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 84 132 3 5 28 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 132 2 7 42 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 84 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 132 12 1 7 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 84 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 84 132 2 5 42 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 84 132 3 3 28 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 84 132 4 2 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 84 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 132 6 1 14 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 84 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 132 4 1 21 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 84 132 3 1 28 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 84 132 2 1 42 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 132
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 84 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 132))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 83 132 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 83 132 (accept_3_4 49 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  83 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 83 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 83 132 (accept_3_4 46 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 83 132 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 83 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 132
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 83 132 (accept_3_4 43 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  83 132 (Polychromatic418967fa.accept_13_3_5_2_1_1475 42 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 83 132 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 83 132 (accept_3_4 40 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 83 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 83 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 132
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 38 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 83 132 (accept_3_4 37 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  83 132 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 83 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 132 (accept_3_4 34 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 132 (Polychromatic418967fa.accept_13_7_5_2_1_401 33 83 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 132
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 132 (accept_3_4 31 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 132 (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 132 (accept_3_4 28 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 132 (Polychromatic418967fa.accept_19_8_7_18_1_1595 27 83 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 132
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 132 (accept_3_4 25 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 132 (Polychromatic418967fa.accept_16_8_3_4_1_3233 24 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 132 (accept_3_4 22 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 83 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 132
  (Polychromatic418967fa.accept_13_7_5_2_1_401 20 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 132 (accept_3_4 19 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 132 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 132 (accept_3_4 16 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 83 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 132
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 132 (accept_3_4 13 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 132 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 132 (accept_3_4 10 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 132 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 83 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 132
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 132 (accept_3_4 7 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  132 (Polychromatic418967fa.accept_16_6_3_4_1_6624 6 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 83 132 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 132 (accept_3_4 4 83 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 83 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 132
  (Polychromatic418967fa.accept_17_2_15_13_1_3034 2 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 132 (accept_3_4 1 83 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  132)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 82 132 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  82 132 2 25 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  49 82 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 82 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 82 132 2 24 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 82 132 (accept_3_5 47 82 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 82 132 2 23 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 82 132 (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 82 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 132 2 22 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 43
  82 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 82 132 2 21 41 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82 132 (accept_3_5 41
  82 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 132 2 20 41 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 82 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 82 132 2 19 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 82 132 (Polychromatic418967fa.accept_13_11_4_2_1_2954 37 82 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 82 132 2 18 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 82 132 (accept_3_5 35 82 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82 132 2 17 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 82 132 (Polychromatic418967fa.accept_15_3_7_12_1_372 33 82 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 132 2 16 41 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 132
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 82 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 132 2 15 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 82 132 (accept_3_5 29 82 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82
  132 2 14 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  82 132 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 82 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 82 132 2 13 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 82 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 82 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 132 2 12 41 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 132 (accept_3_5 23 82 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 132 2 11 41 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 82 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 82 132 2 10 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 82 132 (Polychromatic418967fa.accept_13_6_4_2_1_1433 19 82 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 132 2 9 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 132 (accept_3_5 17 82 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 82 132 2 8 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 82 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 82 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 132 2 7 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 13
  82 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 132 2 6 41 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 132 (accept_3_5 11
  82 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 132 2 5 41 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 132
  (Polychromatic418967fa.accept_19_9_6_18_1_730 9 82 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 132 2 4 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 82 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 132 2 3 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 132 (accept_3_5 5 82 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 132 2 2 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 82 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 132 2 1 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 82
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  132))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 81 132 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  81 132 3 17 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  50 81 132 (Polychromatic418967fa.accept_13_11_3_2_1_863 50 81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 81 132 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 81 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 132 3 16 27 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 132
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 132 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 81 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 81 132 3 15 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 81 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 44
  81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 132
  (Polychromatic418967fa.accept_10_3_1_2_1_521 43 81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 81 132 3 14 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 81 132 (Polychromatic418967fa.accept_21_20_18_6_1_5094 41 81 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 81 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 132 3 13 27 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 132
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 81 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 81 132 3 12 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 81 132 (Polychromatic418967fa.accept_13_9_3_2_1_399 35
  81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 132
  (Polychromatic418967fa.accept_21_13_18_6_1_6676 34 81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 81 132 3 11 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 81 132 (Polychromatic418967fa.accept_15_2_6_12_1_1613 32 81 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 81 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 132 3 10 27 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 132
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 132 (Polychromatic418967fa.accept_16_12_1_4_1_5403 28 81 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 132 3 9 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 81 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 132
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 25 81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 81 132 3 8 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 81 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 81 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 132 (Polychromatic418967fa.accept_13_9_3_2_1_399 22 81 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 132 3 7 27 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 132
  (Polychromatic418967fa.accept_15_5_6_12_1_916 20 81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 81 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 132 3 6 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 81 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 81 132 3 5 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 81 132 (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 81 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 81 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 132 3 4 27 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 132
  (Polychromatic418967fa.accept_13_11_3_2_1_863 11 81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 81 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 132 3 3 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 132 (Polychromatic418967fa.accept_16_8_1_4_1_6622 8 81 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 132
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 81 132 3 2 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 81 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 81 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 132 (Polychromatic418967fa.accept_19_4_5_18_1_6647 4 81 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 132 3 1 27 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 81 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 132 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 81 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 81 132)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 80
  132 (Eq.refl Bool.true) (allA_succ_of_gcd 52 80 132 4 13 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 80 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 80 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 132 2 25 40 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 132 (accept_3_4 49
  80 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 132 4 12 20 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 132
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 80 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 80 132 2 23 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 80 132 (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 80 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 80 132 4 11 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 132 (accept_3_4 43 80 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80 132 2 21 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 80 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 132 4 10 20 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 132
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 80 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 80 132 2 19 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 80 132 (accept_3_4 37 80 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80
  132 4 9 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  80 132 (Polychromatic418967fa.accept_17_1_12_13_1_448 35 80 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 80 132 2 17 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 80 132 (Polychromatic418967fa.accept_17_16_12_13_1_3070 33 80 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 132 4 8 20 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 132 (accept_3_4 31 80 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 132 2 15 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 29
  80 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 80 132 4 7 20 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 80 132
  (Polychromatic418967fa.accept_18_9_8_6_1_4021 27 80 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 80 132 2 13 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 80 132 (accept_3_4 25 80 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80
  132 4 6 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  80 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 80 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 80 132 2 11 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 80 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 80 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 132 4 5 20 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 132 (accept_3_4 19 80 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80 132 2 9 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 80 132 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 80 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 132 4 4 20 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 132
  (Polychromatic418967fa.accept_19_15_4_18_1_5227 15 80 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 80 132 2 7 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 80 132 (accept_3_4 13 80 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80
  132 4 3 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  80 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 80 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 80 132 2 5 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 80 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 80 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 132 4 2 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 132 (accept_3_4 7 80 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 132 2 3 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 80 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 80 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 132 4 1 20 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 132
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 80 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 80 132 2 1 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 80 132 (accept_3_4 1 80 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  132))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 79 132 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 79 132 (accept_3_5 53 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 132 (accept_3_5 50 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 79 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 132
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 132 (accept_3_5 47 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 132 (accept_3_5 44 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 79 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 132
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 42 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 132 (accept_3_5 41 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 132 (accept_3_5 38 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 79 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 132 (accept_3_5 35 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 132 (Polychromatic418967fa.accept_19_15_3_18_1_5241 34 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 132 (Polychromatic418967fa.accept_19_14_3_18_1_6675 33 79 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 132 (accept_3_5 32 79 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 79 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 132
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 132 (accept_3_5 29 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 132 (accept_3_5 26 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 79 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 132 (accept_3_5 23 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 132 (accept_3_5 20 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 79 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 132
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 132 (accept_3_5 17 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 132 (Polychromatic418967fa.accept_13_3_1_2_1_2960 16 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 132 (accept_3_5 14 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 79 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 132
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 132 (accept_3_5 11 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 132 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 132 (accept_3_5 8 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 132 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 79 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 132
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 132 (accept_3_5 5 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  132 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 79 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 79 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 132 (accept_3_5 2 79 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 79 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 132))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 78 132 (Eq.refl Bool.true) (allA_succ_of_gcd 54 78 132 6 9 13 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 132
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 53 78 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 132 2 26 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 78 132 3 17 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 78 132 2 25 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 78 132 (Polychromatic418967fa.accept_14_7_8_6_1_1164 49 78 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 132 6 8 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 78 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 132 2 23 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 78 132 3 15 26 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 78 132 2 22 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 132
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 43 78 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 132 6 7 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 132 (Polychromatic418967fa.accept_16_9_14_4_1_3225 41 78 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 132 2 20 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 132 3 13 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 132 2 19 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 37
  78 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 132 6 6 13 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 132
  (Polychromatic418967fa.accept_10_5_8_2_1_517 35 78 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 132 2 17 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 78 132 3 11 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 78 132 2 16 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 78 132 (Polychromatic418967fa.accept_16_15_14_4_1_6649 31 78 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 132 6 5 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 132 (Polychromatic418967fa.accept_19_10_2_18_1_6674 29 78
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 132 2 14 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 78 132 3 9 26 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 78 132 2 13 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 132
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 78 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 132 6 4 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 78 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 132 2 11 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 78 132 3 7 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 78 132 2 10 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 19
  78 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 132 6 3 13 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 132
  (Polychromatic418967fa.accept_15_2_3_12_1_891 17 78 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 78 132 2 8 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 78 132 3 5 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 78 132 2 7 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 78 132 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 78 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 132 6 2 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 132 (Polychromatic418967fa.accept_21_11_15_6_1_3667 11 78
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 132 2 5 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 78 132 3 3 26 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 78 132 2 4 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 132
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 78 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 132 6 1 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 78 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 132 2 2 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 78 132 3 1 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 78 132 2 1 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 132 (Polychromatic418967fa.accept_16_1_14_4_1_3220 1 78 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  132))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 77 132 (Eq.refl Bool.true) (allA_succ_of_gcd
  55 77 132 11 5 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 77 132 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 77 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 132 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 77 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 132 (accept_3_4 52 77 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 77 132 (Polychromatic418967fa.accept_15_6_2_12_1_885
  51 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 132
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 77 132 (accept_3_4 49 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  77 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 77 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 77 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 132 (accept_3_4 46 77 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 77 132 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 77 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 77 132 11 4 7 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 77 132 (accept_3_4 43 77 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 132 (Polychromatic418967fa.accept_13_3_12_2_1_385 42 77 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 132
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 132 (accept_3_4 40 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 77 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 132 (accept_3_4 37 77 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 132 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 77 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 132
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 132 (accept_3_4 34 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 77
  132 11 3 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  77 132 (Polychromatic418967fa.accept_13_6_12_2_1_4707 32 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 77 132 (accept_3_4 31 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 77 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 77 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 77 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 132 (accept_3_4 28 77 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 77 132 (Polychromatic418967fa.accept_13_1_12_2_1_384
  27 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 132
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 132 (accept_3_4 25 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 132 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 132 (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 77 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 77 132 11 2 7 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 77 132
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 77 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 77 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 132 (accept_3_4 19 77 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 77 132 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 77 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 132
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 132 (accept_3_4 16 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 132 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 132 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 77 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 132 (accept_3_4 13 77 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 77 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 77 132 11 1 7 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 77 132 (accept_3_4 10 77 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 77 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 132
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 132 (accept_3_4 7 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  132 (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 77 132 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 77 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 132 (accept_3_4 4 77 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 77 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 132
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 132 (accept_3_4 1 77 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  132)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 76 132 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 76 132 4 14 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 76 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 132 2 27 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 132 (accept_3_5 53 76 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 132 4 13 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 132 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 76 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 132 2 25 38 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 132
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 49 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 132 4 12 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 132 (accept_3_5 47 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  132 2 23 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  76 132 (Polychromatic418967fa.accept_16_13_12_4_1_4323 45 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 132 4 11 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 76 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 132 2 21 38 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 132 (accept_3_5 41 76 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 132 4 10 19 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 132
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 132 2 19 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 76 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 132 4 9 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 132 (accept_3_5 35 76 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 76 132 2 17 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 76 132 (Polychromatic418967fa.accept_16_1_12_4_1_695 33 76 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 132 4 8 19 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 132
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 132 2 15 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 132 (accept_3_5 29 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  132 4 7 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 132 (Polychromatic418967fa.accept_16_11_12_4_1_3195 27 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 132 2 13 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 76 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 132 4 6 19 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 132 (accept_3_5 23 76 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 132 2 11 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 21
  76 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 132 4 5 19 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 132
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 132 2 9 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 132 (accept_3_5 17 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  132 4 4 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 132 (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 132 2 7 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 76 132 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 76 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 132 4 3 19 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 132 (accept_3_5 11 76 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 132 2 5 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 132 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 76 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 132 4 2 19 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 132
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 132 2 3 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 132 (accept_3_5 5 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 132
  4 1 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  132 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 76 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 132 2 1 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 76 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76 132))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  58 75 132 (Eq.refl Bool.true) (allA_succ_of_gcd 57 75 132 3 19 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 75 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 75 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 132
  (Polychromatic418967fa.accept_8_7_3_4_1_404 55 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 75 132 3 18 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 75 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 75 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 75 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 132 3 17 25 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 132
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 75 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 75 132 3 16 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 47
  75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 46 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 75 132 3 15 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 75 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 75 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 75 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 132 3 14 25 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 132
  (Polychromatic418967fa.accept_9_5_3_6_1_269 41 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 75 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 75 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 75 132 3 13 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 38
  75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 132
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 75 132 3 12 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 75 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 75 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 75 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 132 3 11 25 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 75 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 132 3 10 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 29
  75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 132
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 75 132 3 9 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 75 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 75 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 75 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 132 3 8 25 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 132
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 75 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 132 3 7 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 75 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 75 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 132
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 132 3 6 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 75 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 75 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 132 3 5 25 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 132
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 75 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 132 3 4 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 75 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 132
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 75 132 3 3 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 75 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 75 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 75 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 132 3 2 25 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 132
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 75 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 132 3 1 25 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 75 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 132
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 75 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 132)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 74 132 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 74 132 2 29 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 74 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 74 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 74 132 2 28 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 74 132 (accept_3_4 55 74 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74 132 2 27 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 74 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 74 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 132 2 26 37 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 132 2 25 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 74 132 (accept_3_4 49 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74
  132 2 24 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  74 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 74 132 2 23 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 74 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 74 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 74 132 2 22 37 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 74 132 (accept_3_4 43 74 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74 132 2 21 37 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 74 132
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 74 132 2 20 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 74 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 74 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 132 2 19 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 132 (accept_3_4 37 74 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 132 2 18 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 74 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 132 2 17 37 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 132
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 132 2 16 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 74 132 (accept_3_4 31 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74
  132 2 15 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  74 132 (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 74 132 2 14 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 74 132 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 74 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 132 2 13 37 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 132 (accept_3_4 25 74 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 132 2 12 37 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 74 132 2 11 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 74 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 74 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 132 2 10 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 132 (accept_3_4 19 74 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 132 2 9 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 74 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 74 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 132 2 8 37 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 132
  (Polychromatic418967fa.accept_21_15_11_6_1_5121 15 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 132 2 7 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 132 (accept_3_4 13 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  132 2 6 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 132 (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 132 2 5 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 74 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 132 2 4 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 132 (accept_3_4 7 74 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 132 2 3 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 74 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 132 2 2 37 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 132
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 132 2 1 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 132 (accept_3_4 1 74 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  132))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 73 132 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 73 132 (accept_3_5 59 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 132 (accept_3_5 56 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 132 (Polychromatic418967fa.accept_10_5_3_2_1_899 55 73 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 132
  (Polychromatic418967fa.accept_21_12_10_6_1_1191 54 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 132 (accept_3_5 53 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 132 (accept_3_5 50 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 73 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 132 (accept_3_5 47 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 132 (accept_3_5 44 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 73 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 132
  (Polychromatic418967fa.accept_17_8_5_13_1_4158 42 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 132 (accept_3_5 41 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 132 (accept_3_5 38 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 73 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 132
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 132 (accept_3_5 35 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 132 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 132 (accept_3_5 32 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 73 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 132 (accept_3_5 29 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 132 (Polychromatic418967fa.accept_16_12_9_4_1_4345 28 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 132 (Polychromatic418967fa.accept_16_11_9_4_1_5438 27 73 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 132 (accept_3_5 26 73 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 73 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 132
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 132 (accept_3_5 23 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 132 (accept_3_5 20 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 132 (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 73 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 132
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 132 (accept_3_5 17 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 132 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 132 (accept_3_5 14 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 73 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 132 (accept_3_5 11 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 132 (Polychromatic418967fa.accept_13_10_8_2_1_3829 10 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 132 (accept_3_5 8 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 73 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 132
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 132 (accept_3_5 5 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  132 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 73 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 73 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 132 (accept_3_5 2 73 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 132 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 73 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 132))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 72 132 (Eq.refl Bool.true) (allA_succ_of_gcd 60 72 132 12 5 6 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 72 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 72 132 2 29 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 72 132 3 19 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 72 132 4 14 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 72 132 (Polychromatic418967fa.accept_16_7_8_4_1_689 55 72 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 132 6 9 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 72 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 132 4 13 18 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 72 132 3 17 24 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 72 132 2 25 36 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 132
  (Polychromatic418967fa.accept_16_1_8_4_1_4334 49 72 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 72 132 12 4 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 72 132 (Polychromatic418967fa.accept_13_8_7_2_1_2988 47 72 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 132 2 23 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 72 132 3 15 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 72 132 4 11 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 43
  72 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 132 6 7 12 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 132
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 41 72 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 132 4 10 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 72 132 3 13 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 72 132 2 19 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 72 132 (Polychromatic418967fa.accept_16_5_8_4_1_5418 37 72 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 132 12 3 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 132 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 72 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 132 2 17 36 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 72 132 3 11 24 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 72 132 4 8 18 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 72 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 132 6 5 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 72 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 72 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 132 4 7 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 72 132 3 9 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 72 132 2 13 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 72 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 132 12 2 6 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 132
  (Polychromatic418967fa.accept_16_7_8_4_1_689 23 72 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 72 132 2 11 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 72 132 3 7 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 72 132 4 5 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 132 (Polychromatic418967fa.accept_16_3_8_4_1_3279 19 72 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 132 6 3 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 72 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 132 4 4 18 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 72 132 3 5 24 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 72 132 2 7 36 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 132
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 13 72 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 132 12 1 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 132 2 5 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 72 132 3 3 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 72 132 4 2 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 132 (Polychromatic418967fa.accept_16_7_8_4_1_689 7 72 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 132 6 1 12 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 132
  (Polychromatic418967fa.accept_13_5_7_2_1_852 5 72 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 132 4 1 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 72 132 3 1 24 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 72 132 2 1 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 72 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72 132)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 71 132 (Eq.refl Bool.true) (allA_succ_of_accept 61 71 132 (accept_3_4 61 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 132 (Polychromatic418967fa.accept_13_8_6_2_1_865 60 71 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 132
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 132 (accept_3_4 58 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 56 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 132 (accept_3_4 55 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 71 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 132
  (Polychromatic418967fa.accept_10_3_1_2_1_521 53 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 132 (accept_3_4 52 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 50 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 132 (accept_3_4 49 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 71 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 132
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 132 (accept_3_4 46 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 132 (Polychromatic418967fa.accept_16_13_7_4_1_3248 45 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 132 (accept_3_4 43 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 132 (Polychromatic418967fa.accept_17_8_3_13_1_5372 42 71 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 132
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 132 (accept_3_4 40 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 132 (accept_3_4 37 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 132 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 71 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 132
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 132 (accept_3_4 34 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 132 (accept_3_4 31 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 71 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 132
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 132 (accept_3_4 28 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 132 (accept_3_4 25 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 132 (Polychromatic418967fa.accept_16_8_7_4_1_2217 24 71 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 132
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 132 (accept_3_4 22 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 132 (accept_3_4 19 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 132 (Polychromatic418967fa.accept_24_18_23_12_1_6673 18 71 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 132
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 132 (accept_3_4 16 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 132 (Polychromatic418967fa.accept_18_15_17_6_1_4043 15 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 132 (accept_3_4 13 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 132
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 132 (accept_3_4 10 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 132 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 132 (accept_3_4 7 71 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 132 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 71 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 132
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 132 (accept_3_4 4 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  132 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 71 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 71 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 132 (accept_3_4 1 71 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 132)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 70 132
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 70 132 2 31 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 70 132 (Polychromatic418967fa.accept_13_9_5_2_1_2185 61 70 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 132 2 30 35 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 132 (accept_3_5 59 70 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70 132 2 29 35 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 70 132
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 70 132 2 28 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 70 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 70 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 70 132 2 27 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 132 (accept_3_5 53 70 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 132 2 26 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 132 (Polychromatic418967fa.accept_13_12_5_2_1_2173 51 70 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 132 2 25 35 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 132
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 70 132 2 24 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 70 132 (accept_3_5 47 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70
  132 2 23 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  70 132 (Polychromatic418967fa.accept_16_13_6_4_1_3277 45 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 70 132 2 22 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 70 132 (Polychromatic418967fa.accept_13_4_5_2_1_1436 43 70 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 132 2 21 35 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 132 (accept_3_5 41 70 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 132 2 20 35 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 132
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 70 132 2 19 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 70 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 70 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 132 2 18 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 70 132 (accept_3_5 35 70 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70 132 2 17 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 132 (Polychromatic418967fa.accept_13_7_5_2_1_401 33 70 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 132 2 16 35 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 132
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 70 132 2 15 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 70 132 (accept_3_5 29 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70
  132 2 14 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  70 132 (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 70 132 2 13 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 70 132 (Polychromatic418967fa.accept_13_12_5_2_1_2173 25 70 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 132 2 12 35 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 132 (accept_3_5 23 70 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 132 2 11 35 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 132
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 132 2 10 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 70 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 132 2 9 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 132 (accept_3_5 17 70 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 70 132 2 8 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 70 132 (Polychromatic418967fa.accept_17_15_2_13_1_4153 15 70 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 132 2 7 35 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 132
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 70 132 2 6 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 70 132 (accept_3_5 11 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  132 2 5 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 132 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 70 132 2 4 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 70 132 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 70 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 132 2 3 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 132 (accept_3_5 5 70 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 132 2 2 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 70 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 70 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 132 2 1 35 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 132
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 70 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 132))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 69 132 (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 69 132 3 21 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 69 132 (Polychromatic418967fa.accept_20_2_9_12_1_2546 62 69 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 132 (Polychromatic418967fa.accept_10_1_9_2_1_45 61
  69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 69 132 3 20 23 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 69 132
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 59 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 69 132 (Polychromatic418967fa.accept_13_6_4_2_1_1433 58 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 132 3 19 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 132 (Polychromatic418967fa.accept_16_8_5_4_1_674 56
  69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 132
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 55 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 69 132 3 18 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 69 132 (Polychromatic418967fa.accept_17_2_1_13_1_6670 53 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 132 (Polychromatic418967fa.accept_18_16_15_6_1_4039 52 69
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 69 132 3 17 23 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 69 132
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 50 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 132 3 16 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 132 (Polychromatic418967fa.accept_10_7_9_2_1_1887
  47 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 132
  (Polychromatic418967fa.accept_17_12_1_13_1_6672 46 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 69 132 3 15 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 69 132 (Polychromatic418967fa.accept_13_5_4_2_1_846 44 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 132 (Polychromatic418967fa.accept_20_3_9_12_1_6671 43 69
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 132 3 14 23 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 132
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 132 (Polychromatic418967fa.accept_14_12_13_6_1_1140 40 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 132 3 13 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 132 (Polychromatic418967fa.accept_13_12_4_2_1_2955
  38 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 132
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 69 132 3 12 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 69 132 (Polychromatic418967fa.accept_14_7_13_6_1_1177 35 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 132 (Polychromatic418967fa.accept_15_4_9_12_1_2495 34 69
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 132 3 11 23 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 132
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 32 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 132 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 132 3 10 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 132 (Polychromatic418967fa.accept_15_14_9_12_1_2498
  29 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 132
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 28 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 69 132 3 9 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 69 132 (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 69 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 132 3 8 23 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 132
  (Polychromatic418967fa.accept_18_5_15_6_1_3999 23 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 132 (Polychromatic418967fa.accept_16_6_5_4_1_4330 22 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 132 3 7 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 132 (Polychromatic418967fa.accept_15_5_9_12_1_1599 20 69 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 132
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 19 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 69 132 3 6 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 69 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 132 (Polychromatic418967fa.accept_18_16_15_6_1_4039 16 69
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 132 3 5 23 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 132
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 14 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 132 (Polychromatic418967fa.accept_19_13_12_18_1_2677 13 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 132 3 4 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 132 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 69 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 132
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 132 3 3 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 132 (Polychromatic418967fa.accept_16_8_5_4_1_674 8 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 132 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 69 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 132 3 2 23 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 132
  (Polychromatic418967fa.accept_13_5_4_2_1_846 5 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 132 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 69 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 132 3 1 23 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 132 (Polychromatic418967fa.accept_17_2_1_13_1_6670 2 69 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 132
  (Polychromatic418967fa.accept_8_1_5_4_1_388 1 69 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 132)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 68 132 (Eq.refl
  Bool.true) (allA_succ_of_gcd 64 68 132 4 16 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 68 132 (Polychromatic418967fa.accept_13_11_3_2_1_863 63 68 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 132 2 31 34 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 132 (accept_3_4 61 68 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 132 4 15 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 132
  (Polychromatic418967fa.accept_24_11_20_12_1_6669 59 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 68 132 2 29 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 68 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 68 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 68 132 4 14 17 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 68 132 (accept_3_4 55 68 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68 132 2 27 34 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 68 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 68 132 4 13 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 68 132 (Polychromatic418967fa.accept_13_12_3_2_1_1470 51 68 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 132 2 25 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 132 (accept_3_4 49 68 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 132 4 12 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 68 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 132 2 23 34 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 132
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 68 132 4 11 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 68 132 (accept_3_4 43 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68
  132 2 21 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  68 132 (Polychromatic418967fa.accept_14_13_12_6_1_2735 41 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 68 132 4 10 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 68 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 68 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 132 2 19 34 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 132 (accept_3_4 37 68 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 132 4 9 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 68 132 (Polychromatic418967fa.accept_9_8_5_6_1_538 35
  68 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 132 2 17 34 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 132
  (Polychromatic418967fa.accept_15_3_8_12_1_900 33 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 132 4 8 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 132 (accept_3_4 31 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  132 2 15 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  68 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 132 4 7 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 68 132 (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 68 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 132 2 13 34 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 132 (accept_3_4 25 68 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 132 4 6 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 132 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 68 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 132 2 11 34 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 132
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 132 4 5 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 132 (accept_3_4 19 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  132 2 9 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 132 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 132 4 4 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 68 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 132 2 7 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 132 (accept_3_4 13 68 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 132 4 3 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 68 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 68 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 132 2 5 34 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 132
  (Polychromatic418967fa.accept_13_9_3_2_1_399 9 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 132 4 2 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 132 (accept_3_4 7 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 132
  2 3 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  132 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 68 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 132 4 1 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 68 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 132 2 1 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 132 (accept_3_4 1 68 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 132))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 67 132
  (Eq.refl Bool.true) (allA_succ_of_accept 65 67 132 (accept_3_5 65 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 67 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 67 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 67 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 67 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 132 (accept_3_5 62 67 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 61
  67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 132
  (Polychromatic418967fa.accept_16_12_3_4_1_4317 60 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 132 (accept_3_5 59 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 132 (accept_3_5 56 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 67 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 132
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 132 (accept_3_5 53 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 132 (accept_3_5 50 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 132 (Polychromatic418967fa.accept_10_9_7_2_1_887 49 67 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 132
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 132 (accept_3_5 47 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 132 (accept_3_5 44 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 67 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 132
  (Polychromatic418967fa.accept_20_2_7_12_1_5215 42 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 132 (accept_3_5 41 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 132 (accept_3_5 38 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 67 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 132
  (Polychromatic418967fa.accept_15_6_7_12_1_869 36 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 132 (accept_3_5 35 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 132 (accept_3_5 32 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 67 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 132 (accept_3_5 29 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 132 (Polychromatic418967fa.accept_18_9_13_6_1_877 27 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 132 (accept_3_5 26 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 67 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 132
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 132 (accept_3_5 23 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 132 (Polychromatic418967fa.accept_16_6_3_4_1_6624 22 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 132 (accept_3_5 20 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 67 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 132
  (Polychromatic418967fa.accept_15_3_7_12_1_372 18 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 132 (accept_3_5 17 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 132 (accept_3_5 14 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 132 (Polychromatic418967fa.accept_21_13_4_6_1_6668 13 67 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 132
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 132 (accept_3_5 11 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 132 (accept_3_5 8 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 67 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 132
  (Polychromatic418967fa.accept_15_6_7_12_1_869 6 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 132 (accept_3_5 5 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  132 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 67 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 67 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 132 (accept_3_5 2 67 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 67 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  132)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 132 (allA_succ_of_accept 65 66 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 66 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 132 2 32 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 66 132 3 21 22 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 66 132 2 31 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 66 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 132 6 10 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  66 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 132 2 29 33 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 66 132 3 19 22 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 66 132 2 28 33 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 66 132 11 5 6 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 66 132 6 9 11 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 132
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 66 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 66 132 2 26 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 66 132 3 17 22 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 66 132 2 25 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 66 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 66 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 132 6 8 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 66 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 132 2 23 33 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 66 132 3 15 22 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 66 132 22 2 3 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 66 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 132 6 7 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 66 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 132 2 20 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 66 132 3 13 22 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 66 132 2 19 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 66
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 132 6 6 11 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 132
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 66 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 66 132 2 17 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 66 132 33 1 2 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 66 132 2 16 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 66 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 66 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 132 6 5 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 66 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 132 2 14 33 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 66 132 3 9 22 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 66 132 2 13 33 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 132
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 66 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 132 6 4 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 66 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 132 22 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 132 3 7 22 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 66 132 2 10 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 66 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 132 6 3 11 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 132
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 66 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 66 132 2 8 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 66 132 3 5 22 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 66 132 2 7 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 66 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 66 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 132 6 2 11 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 66 132 11 1 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 66 132 2 5 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 66 132 3 3 22 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 66 132 2 4 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 66 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 132 6 1 11 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 132
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 66 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 132 2 2 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 66 132 3 1 22 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 66 132 2 1 33 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 66 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 132))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 132 (allA_succ_of_accept 64 65 132 (accept_3_4 64 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 65 132 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 65 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 62 65 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 132 (accept_3_4 61 65 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 60
  65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 132 (accept_3_4 58 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 132 (Polychromatic418967fa.accept_16_8_1_4_1_6622 56 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 132 (accept_3_4 55 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 132 (Polychromatic418967fa.accept_15_9_5_12_1_1640 54 65 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 132
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 132 (accept_3_4 52 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 132 (Polychromatic418967fa.accept_15_6_5_12_1_1642 51 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 132 (accept_3_4 49 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 65 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 132
  (Polychromatic418967fa.accept_10_7_5_2_1_880 47 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 132 (accept_3_4 46 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 132 (accept_3_4 43 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 132 (Polychromatic418967fa.accept_19_4_8_18_1_5268 42 65 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 132
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 132 (accept_3_4 40 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 132 (accept_3_4 37 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 65 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 132
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 132 (accept_3_4 34 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 132 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 132 (accept_3_4 31 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 65 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 132 (accept_3_4 28 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 132 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 132 (accept_3_4 25 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 132
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 132 (accept_3_4 22 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 132 (Polychromatic418967fa.accept_19_1_8_18_1_6667 20 65 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 132 (accept_3_4 19 65 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 65 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 132 (accept_3_4 16 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 132 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 132 (accept_3_4 13 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 65 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 132
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 132 (accept_3_4 10 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 132 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 132 (accept_3_4 7 65 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 132 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 65 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 132
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 132 (accept_3_4 4 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  132 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 65 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 132 (Polychromatic418967fa.accept_15_2_5_12_1_369 2 65 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 132 (accept_3_4 1 65 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 132))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 132
  (allA_succ_of_accept 63 64 132 (Polychromatic418967fa.accept_14_7_8_6_1_1164 63 64 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 64 132 2 31 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 64 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 61
  64 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 132 4 15 16 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 132 (accept_3_5 59
  64 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 132 2 29 32 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 57 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 132 4 14 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 132 (Polychromatic418967fa.accept_13_3_12_2_1_385 55 64 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 132 2 27 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 132 (accept_3_5 53 64 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 132 4 13 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 64 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 132 2 25 32 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 132
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 132 4 12 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 132 (accept_3_5 47 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  132 2 23 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 132 (Polychromatic418967fa.accept_13_6_12_2_1_4707 45 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 132 4 11 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 64 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 132 2 21 32 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 132 (accept_3_5 41 64 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 132 4 10 16 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 64 132 2 19 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 64 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 64 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 132 4 9 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 132 (accept_3_5 35 64 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 64 132 2 17 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 64 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 64 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 132 4 8 16 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 132
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 132 2 15 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 132 (accept_3_5 29 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  132 4 7 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 132 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 132 2 13 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 64 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 132 4 6 16 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 132 (accept_3_5 23 64 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 132 2 11 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  64 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 132 4 5 16 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 132
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 132 2 9 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 132 (accept_3_5 17 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  132 4 4 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 132 (Polychromatic418967fa.accept_18_15_10_6_1_1781 15 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 132 2 7 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 64 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 64 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 132 4 3 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 132 (accept_3_5 11 64 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 132 2 5 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 64 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 64 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 132 4 2 16 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 132
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 64 132 2 3 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 64 132 (accept_3_5 5 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 132
  4 1 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64
  132 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 64 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 132 2 1 32 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 132 (Polychromatic418967fa.accept_13_1_12_2_1_384 1 64 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 132))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 63 132 (allA_succ_of_accept 62 63 132 (Polychromatic418967fa.accept_13_10_11_2_1_3862 62 63 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 132
  (Polychromatic418967fa.accept_10_1_3_2_1_220 61 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 63 132 3 20 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 63 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 132 (Polychromatic418967fa.accept_15_13_3_12_1_1609 58 63
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 63 132 3 19 21 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 63 132
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 56 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 132 (Polychromatic418967fa.accept_10_5_3_2_1_899 55 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 132 3 18 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 132 (Polychromatic418967fa.accept_15_8_3_12_1_1657
  53 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 132
  (Polychromatic418967fa.accept_15_7_3_12_1_365 52 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 63 132 3 17 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 63 132 (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 132 (Polychromatic418967fa.accept_13_10_11_2_1_3862 49 63
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 63 132 3 16 21 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 132
  (Polychromatic418967fa.accept_15_2_3_12_1_891 47 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 132 (Polychromatic418967fa.accept_16_14_15_4_1_3268 46 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 132 3 15 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 132 (Polychromatic418967fa.accept_16_12_15_4_1_5422
  44 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 132
  (Polychromatic418967fa.accept_8_3_7_4_1_42 43 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 63 132 3 14 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 63 132 (Polychromatic418967fa.accept_10_1_3_2_1_220 41 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 132 (Polychromatic418967fa.accept_16_8_15_4_1_5402 40 63
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 132 3 13 21 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 132
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 38 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 132 (Polychromatic418967fa.accept_15_7_3_12_1_365 37 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 132 3 12 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 35
  63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 132
  (Polychromatic418967fa.accept_25_9_13_7_1_6666 34 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 63 132 3 11 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 63 132 (Polychromatic418967fa.accept_15_2_3_12_1_891 32 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 132 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 63 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 132 3 10 21 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 132
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 63 132 (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 132 3 9 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 132 (Polychromatic418967fa.accept_18_8_9_6_1_3989 26 63 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 132
  (Polychromatic418967fa.accept_10_5_3_2_1_899 25 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 63 132 3 8 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 63 132 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 132 (Polychromatic418967fa.accept_13_9_11_2_1_1491 22 63
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 132 3 7 21 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 132
  (Polychromatic418967fa.accept_18_2_9_6_1_4025 20 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 132 3 6 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 132 (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 63 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 132
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 63 132 3 5 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 63 132 (Polychromatic418967fa.accept_16_14_15_4_1_3268 14 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 132 (Polychromatic418967fa.accept_14_13_7_6_1_3525 13 63
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 132 3 4 21 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 132
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 132 (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 132 3 3 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 132 (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 63 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 132
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 63 132 3 2 21 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 63 132 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 132 (Polychromatic418967fa.accept_13_4_11_2_1_1458 4 63 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 132 3 1 21 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 132
  (Polychromatic418967fa.accept_15_2_3_12_1_891 2 63 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 132 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 63 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 132)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 62 132 (allA_succ_of_accept 61 62 132 (accept_3_4 61 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 62 132 2 30 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 62 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 62 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 62 132 2 29 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 62 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 57
  62 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 132 2 28 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 132 (accept_3_4 55
  62 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 132 2 27 31 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 132
  (Polychromatic418967fa.accept_21_11_20_6_1_6641 53 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 62 132 2 26 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 62 132 (Polychromatic418967fa.accept_13_12_10_2_1_1451 51 62 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 62 132 2 25 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 62 132 (accept_3_4 49 62 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62 132 2 24 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 62 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 62 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 132 2 23 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 132
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 132 2 22 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 62 132 (accept_3_4 43 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62
  132 2 21 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  62 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 62 132 2 20 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 62 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 62 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 132 2 19 31 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 132 (accept_3_4 37 62 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 132 2 18 31 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 132
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 35 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 62 132 2 17 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 62 132 (Polychromatic418967fa.accept_15_3_2_12_1_2469 33 62 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 62 132 2 16 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 62 132 (accept_3_4 31 62 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62 132 2 15 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 62 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 62 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 132 2 14 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 132
  (Polychromatic418967fa.accept_18_9_8_6_1_4021 27 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 132 2 13 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 62 132 (accept_3_4 25 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62
  132 2 12 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  62 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 62 132 2 11 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 62 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 62 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 132 2 10 31 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 132 (accept_3_4 19 62 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 132 2 9 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 62 132 (Polychromatic418967fa.accept_16_1_14_4_1_3220
  17 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 132 2 8 31 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 132
  (Polychromatic418967fa.accept_16_15_14_4_1_6649 15 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 132 2 7 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 132 (accept_3_4 13 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  132 2 6 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 132 2 5 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 132 (Polychromatic418967fa.accept_16_9_14_4_1_3225 9 62 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 132 2 4 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 132 (accept_3_4 7 62 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 132 2 3 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 62 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 132 2 2 31 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 132
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 132 2 1 31 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 132 (accept_3_4 1 62 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  132)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 132 (allA_succ_of_accept 60 61 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 132 (accept_3_5 59 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 132 (accept_3_5 56 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 61 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 132
  (Polychromatic418967fa.accept_16_6_13_4_1_643 54 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 132 (accept_3_5 53 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 132 (Polychromatic418967fa.accept_19_14_4_18_1_6665 52 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 132 (Polychromatic418967fa.accept_20_11_1_12_1_3803 51 61 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 132 (accept_3_5 50 61 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 61 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 132
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 132 (accept_3_5 47 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 132 (Polychromatic418967fa.accept_13_6_9_2_1_838 45 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 132 (accept_3_5 44 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 61 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 132
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 42 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 132 (accept_3_5 41 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 132 (accept_3_5 38 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 61 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 132
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 132 (accept_3_5 35 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 132 (Polychromatic418967fa.accept_15_4_1_12_1_914 34 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 132 (accept_3_5 32 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 61 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 132
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 132 (accept_3_5 29 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 132 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 132 (accept_3_5 26 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 61 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 132
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 132 (accept_3_5 23 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 132 (accept_3_5 20 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 61 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 132 (accept_3_5 17 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 132 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 132 (accept_3_5 14 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 61 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 132
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 132 (accept_3_5 11 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 132 (accept_3_5 8 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 132 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 61 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 132
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 132 (accept_3_5 5 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  132 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 61 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 61 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 132 (accept_3_5 2 61 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 132)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 132 (allA_succ_of_accept 59 60 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 60 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 132 2 29 30 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 60 132 3 19 20 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 60 132 4 14 15 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 132
  (Polychromatic418967fa.accept_16_7_12_4_1_1347 55 60 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 60 132 6 9 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 60 132 (Polychromatic418967fa.accept_16_5_12_4_1_4325 53 60 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 132 4 13 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 60 132 3 17 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 60 132 2 25 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 132 (Polychromatic418967fa.accept_13_10_8_2_1_3829
  49 60 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 132 12 4 5 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 132
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 60 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 60 132 2 23 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 60 132 3 15 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 60 132 4 11 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 60 132 (Polychromatic418967fa.accept_16_11_12_4_1_3195 43 60 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 132 6 7 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 132 (Polychromatic418967fa.accept_16_9_12_4_1_3255 41 60 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 132 4 10 15 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 132 3 13 20 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 60 132 2 19 30 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 60 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 132 12 3 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 60 132 (Polychromatic418967fa.accept_16_3_12_4_1_170 35 60 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 132 2 17 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 60 132 3 11 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 60 132 4 8 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 31
  60 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 132 6 5 10 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 132
  (Polychromatic418967fa.accept_16_13_12_4_1_4323 29 60 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 60 132 4 7 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 60 132 3 9 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 60 132 2 13 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 60 132 (Polychromatic418967fa.accept_16_9_12_4_1_3255 25 60 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 132 12 2 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 132 2 11 30 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 132 3 7 20 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 132 4 5 15 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 132
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 60 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 132 6 3 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 132 4 4 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 132 3 5 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 132 2 7 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 132 (Polychromatic418967fa.accept_16_13_12_4_1_4323 13 60
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 132 12 1 5 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 132
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 11 60 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 132 2 5 30 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 60 132 3 3 20 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 60 132 4 2 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 132 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 60 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 132 6 1 10 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 60 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 132 4 1 15 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 132 3 1 20 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 132 2 1 30 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 132
  (Polychromatic418967fa.accept_16_1_12_4_1_695 1 60 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 132)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 132 (allA_succ_of_accept 58
  59 132 (accept_3_4 58 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 132
  (Polychromatic418967fa.accept_9_3_5_6_1_253 57 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 56 59 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 132 (accept_3_4 55 59 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 132 (Polychromatic418967fa.accept_15_9_14_12_1_913 54 59 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 132
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 132 (accept_3_4 52 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 132 (Polychromatic418967fa.accept_23_4_13_17_1_6664 50 59 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 132 (accept_3_4 49 59 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 59 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 132
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 132 (accept_3_4 46 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 132 (Polychromatic418967fa.accept_24_21_11_12_1_6663 45 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 59 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 132 (accept_3_4 43 59 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 132 (Polychromatic418967fa.accept_19_4_2_18_1_6662 42 59 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 132
  (Polychromatic418967fa.accept_10_1_9_2_1_45 41 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 132 (accept_3_4 40 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 59 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 132 (accept_3_4 37 59 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 132 (Polychromatic418967fa.accept_21_15_17_6_1_6661 36 59 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 132
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 132 (accept_3_4 34 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 132 (Polychromatic418967fa.accept_18_15_5_6_1_5293 33 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 59 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 132 (accept_3_4 31 59 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 59 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 132
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 132 (accept_3_4 28 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 132 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 132 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 59 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 132 (accept_3_4 25 59 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 132 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 59 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 132 (accept_3_4 22 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 59 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 132 (accept_3_4 19 59 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 59 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 132
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 132 (accept_3_4 16 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 132 (Polychromatic418967fa.accept_25_14_9_7_1_6660 14 59 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 132 (accept_3_4 13 59 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 59 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 132
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 132 (accept_3_4 10 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 132 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 59 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 132 (accept_3_4 7 59 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 132 (Polychromatic418967fa.accept_16_6_11_4_1_635 6 59 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 132 (Polychromatic418967fa.accept_13_5_7_2_1_852 5
  59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 132 (accept_3_4 4 59 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 132 (accept_3_4 1 59 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  132))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 132 (allA_succ_of_accept 57 58 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 58 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 132 2 28 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 58 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 58 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 132 2 27 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 132 (accept_3_5 53 58 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 132 2 26 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 132 (Polychromatic418967fa.accept_13_12_6_2_1_1441 51 58 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 132 2 25 29 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 132
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 49 58 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 132 2 24 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 132 (accept_3_5 47 58 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58
  132 2 23 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  58 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 58 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 132 2 22 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 58 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 132 2 21 29 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 132 (accept_3_5 41 58 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 132 2 20 29 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 132
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 58 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 132 2 19 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 58 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 132 2 18 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 132 (accept_3_5 35 58 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 132 2 17 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 132 (Polychromatic418967fa.accept_15_3_13_12_1_348 33 58 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 132 2 16 29 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 58 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 132 2 15 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 132 (accept_3_5 29 58 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  132 2 14 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 132 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 58 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 132 2 13 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 58 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 132 2 12 29 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 132 (accept_3_5 23 58 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 132 2 11 29 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 132
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 58 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 132 2 10 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 58 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 132 2 9 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 132 (accept_3_5 17 58 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 132 2 8 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 58 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 132 2 7 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 132 (Polychromatic418967fa.accept_19_13_1_18_1_5279
  13 58 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 132 2 6 29 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 132 (accept_3_5 11
  58 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 132 2 5 29 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 132
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 58 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 132 2 4 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 58 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 132 2 3 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 132 (accept_3_5 5 58 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 132 2 2 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 58 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 132 2 1 29 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 58
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  132)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 132 (allA_succ_of_accept 56 57 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 132 3 18 19 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 53
  57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 132 3 17 19 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 57 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 132 3 16 19 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 132
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 132 3 15 19 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 44
  57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 132 3 14 19 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 57 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 132 3 13 19 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 132 3 12 19 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 132 3 11 19 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 57 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 132 3 10 19 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 132
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 132 3 9 19 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 57 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 132 3 8 19 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 57 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 132 3 7 19 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 132 3 6 19 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 57 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 132
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 132 3 5 19 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 57 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 132 3 4 19 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 132 3 3 19 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 132 3 2 19 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 57 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 132 3 1 19 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 132
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 57 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 132))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 132 (allA_succ_of_accept 55 56 132 (accept_3_4 55 56 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  54 56 132 2 27 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 56 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 132 4 13 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 132 (Polychromatic418967fa.accept_10_1_6_2_1_867 51
  56 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 132 2 25 28 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 132 (accept_3_4 49
  56 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 132 4 12 14 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 132
  (Polychromatic418967fa.accept_16_15_8_4_1_1355 47 56 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 132 2 23 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 132 (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 56 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 132 4 11 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 132 (accept_3_4 43 56 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 132 2 21 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 132 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 56 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 132 4 10 14 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 132
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 132 2 19 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 132 (accept_3_4 37 56 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  132 4 9 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 56 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 132 2 17 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 132 (Polychromatic418967fa.accept_16_1_8_4_1_4334 33 56 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 132 4 8 14 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 132 (accept_3_4 31 56 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 132 2 15 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 132
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 29 56 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 132 4 7 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 56 132 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 56 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 132 2 13 28 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 132 (accept_3_4 25 56 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 132 4 6 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 132 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 56 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 132 2 11 28 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 132
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 132 4 5 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 132 (accept_3_4 19 56 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  132 2 9 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 56 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 132 4 4 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 132 (Polychromatic418967fa.accept_16_15_8_4_1_1355 15 56 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 132 2 7 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 132 (accept_3_4 13 56 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 132 4 3 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 56 132 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 56 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 132 2 5 28 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 132
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 56 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 132 4 2 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 132 (accept_3_4 7 56 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 132
  2 3 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  132 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 56 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 132 4 1 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 132 2 1 28 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 132 (accept_3_4 1 56 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 132)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 132
  (allA_succ_of_accept 54 55 132 (Polychromatic418967fa.accept_14_12_13_6_1_1140 54 55 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 132 (accept_3_5 53 55 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 55 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 51
  55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 132 (accept_3_5 50 55
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 132
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 55 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 132 (accept_3_5 47 55 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 132 (Polychromatic418967fa.accept_16_14_7_4_1_3243 46 55 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 132
  (Polychromatic418967fa.accept_16_13_7_4_1_3248 45 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 55 132 11 4 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 55 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 55 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 132 (Polychromatic418967fa.accept_17_8_4_13_1_3014 42 55
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 132 (accept_3_5 41 55 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 40
  55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 132 (accept_3_5 38 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 132 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 132 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 55 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 132 (accept_3_5 35 55 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 55 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 55 132 11 3 5 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 55 132 (accept_3_5 32 55 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 31
  55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 132 (accept_3_5 29 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 132 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 55 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 132 (accept_3_5 26 55 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 55 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 132
  (Polychromatic418967fa.accept_13_11_3_2_1_863 24 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 132 (accept_3_5 23 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 55
  132 11 2 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  55 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 55 132 (accept_3_5 20 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 55 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 55 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 132 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 55 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 132 (accept_3_5 17 55 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 16
  55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 132
  (Polychromatic418967fa.accept_21_15_13_6_1_6659 15 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 132 (accept_3_5 14 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 55 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 55 132 11 1 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 55 132 (Polychromatic418967fa.accept_13_10_3_2_1_4728
  10 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 132
  (Polychromatic418967fa.accept_13_9_3_2_1_399 9 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 132 (accept_3_5 8 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  132 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 132 (Polychromatic418967fa.accept_15_6_10_12_1_2538 6 55 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 132 (accept_3_5 5 55 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 55 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 55
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 132 (accept_3_5 2 55 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 132 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1
  55 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  132))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 132 (allA_succ_of_accept 53 54 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 54 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 132 2 26 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 54 132 3 17 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 54 132 2 25 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 132 (Polychromatic418967fa.accept_15_4_9_12_1_2495 49 54 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 132 6 8 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 132 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 54 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 132 2 23 27 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 54 132 3 15 18 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 54 132 2 22 27 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 132
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 54 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 132 6 7 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 132 (Polychromatic418967fa.accept_14_13_12_6_1_2735 41 54 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 132 2 20 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 54 132 3 13 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 54 132 2 19 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 132 (Polychromatic418967fa.accept_10_7_4_2_1_903 37
  54 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 132 6 6 9 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 132
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 35 54 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 132 2 17 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 54 132 3 11 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 54 132 2 16 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 132 (Polychromatic418967fa.accept_21_10_12_6_1_5124 31 54 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 132 6 5 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 54 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 132 2 14 27 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 54 132 3 9 18 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 54 132 2 13 27 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 54 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 132 6 4 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 132 (Polychromatic418967fa.accept_21_2_12_6_1_6658 23 54 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 132 2 11 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 54 132 3 7 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 54 132 2 10 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 132 (Polychromatic418967fa.accept_15_4_9_12_1_2495
  19 54 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 132 6 3 9 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 132
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 54 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 54 132 2 8 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 54 132 3 5 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 54 132 2 7 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 132 (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 54 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 132 6 2 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 54 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 132 2 5 27 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 132 3 3 18 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 132 2 4 27 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 132
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 54 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 132 6 1 9 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 132 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 54 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 132 2 2 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 54 132 3 1 18 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 54 132 2 1 27 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 54 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  132)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 132 (allA_succ_of_accept 52 53 132 (accept_3_4
  52 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 50 53 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 132 (accept_3_4 49 53 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 132 (accept_3_4 46 53
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 132
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 53 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 132 (accept_3_4 43 53 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 132 (Polychromatic418967fa.accept_13_3_1_2_1_2960 42 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 41
  53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 132 (accept_3_4 40 53
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 132 (Polychromatic418967fa.accept_9_3_8_6_1_80
  39 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 132
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 132 (accept_3_4 37 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 132 (Polychromatic418967fa.accept_21_15_11_6_1_5121 36 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 132 (Polychromatic418967fa.accept_10_5_3_2_1_899 35 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 132 (accept_3_4 34 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 53 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 132
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 132 (accept_3_4 31 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 132 (accept_3_4 28 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 132 (Polychromatic418967fa.accept_24_3_5_12_1_6657 27 53 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 132
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 132 (accept_3_4 25 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 132 (accept_3_4 22 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 132
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 132 (accept_3_4 19 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 132 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 132 (accept_3_4 16 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 132 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 53 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 132
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 132 (accept_3_4 13 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 132 (accept_3_4 10 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 53 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 132
  (Polychromatic418967fa.accept_16_8_5_4_1_674 8 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 132 (accept_3_4 7 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  132 (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 53 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 132 (accept_3_4 4 53 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 53 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 53 132 (accept_3_4 1 53 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53
  132))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 132 (allA_succ_of_accept 51 52 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 132 2 25 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 52 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 132 4 12 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 132 (accept_3_5 47 52 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 132 2 23 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 132 (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 52 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 132 4 11 13 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 132
  (Polychromatic418967fa.accept_24_19_4_12_1_6656 43 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 132 2 21 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 132 (accept_3_5 41 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  132 4 10 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 132 2 19 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 52 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 132 4 9 13 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 132 (accept_3_5 35 52 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 132 2 17 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 132 (Polychromatic418967fa.accept_15_3_7_12_1_372
  33 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 132 4 8 13 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 132
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 132 2 15 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 52 132 (accept_3_5 29 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52
  132 4 7 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  52 132 (Polychromatic418967fa.accept_23_4_6_17_1_6655 27 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 52 132 2 13 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 52 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 52 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 132 4 6 13 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 132 (accept_3_5 23 52 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 132 2 11 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  52 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 132 4 5 13 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 132
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 132 2 9 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 132 (accept_3_5 17 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  132 4 4 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 132 (Polychromatic418967fa.accept_18_15_16_6_1_1751 15 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 132 2 7 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 52 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 52 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 132 4 3 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 132 (accept_3_5 11 52 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 132 2 5 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 52 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 52 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 132 4 2 13 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 132
  (Polychromatic418967fa.accept_19_7_14_18_1_6654 7 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 52 132 2 3 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 52 132 (accept_3_5 5 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 132
  4 1 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52
  132 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 132 2 1 26 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 52 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 132)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 132
  (allA_succ_of_accept 50 51 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 51 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 132 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 51 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 132 3 16 17 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 132
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 51 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 51 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 132 3 15 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 132 (Polychromatic418967fa.accept_13_5_12_2_1_1423
  44 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 51 132 3 14 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 51 132 (Polychromatic418967fa.accept_18_5_15_6_1_3999 41 51 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 132 (Polychromatic418967fa.accept_13_1_12_2_1_384 40 51 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 132 3 13 17 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 132 (Polychromatic418967fa.accept_15_7_6_12_1_1614 37 51 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 132 3 12 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 132 (Polychromatic418967fa.accept_15_5_6_12_1_916
  35 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 132
  (Polychromatic418967fa.accept_18_16_15_6_1_4039 34 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 51 132 3 11 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 51 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 51 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 51 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 132 3 10 17 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 132 (Polychromatic418967fa.accept_16_12_3_4_1_4317 28 51 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 132 3 9 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 132 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 51 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 132
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 51 132 3 8 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 51 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 51 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 51 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 132 3 7 17 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 132
  (Polychromatic418967fa.accept_15_5_6_12_1_916 20 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 132 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 51 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 132 3 6 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 51 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 132
  (Polychromatic418967fa.accept_10_6_1_2_1_874 16 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 51 132 3 5 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 132 (Polychromatic418967fa.accept_13_1_12_2_1_384 14 51 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 132 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 51 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 132 3 4 17 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 132
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 51 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 132 3 3 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 51 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 132
  (Polychromatic418967fa.accept_8_7_3_4_1_404 7 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 132 3 2 17 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 132 (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 51 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 51 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 132 3 1 17 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 132
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 51 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 51 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 51 132))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 132
  (allA_succ_of_accept 49 50 132 (accept_3_4 49 50 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50
  132 2 24 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  50 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 50 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 50 132 2 23 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 50 132 (Polychromatic418967fa.accept_18_9_14_6_1_1790 45 50 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 132 2 22 25 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 132 (accept_3_4 43 50 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 132 2 21 25 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 132
  (Polychromatic418967fa.accept_36_5_14_24_1_6653 41 50 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 132 2 20 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 50 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 132 2 19 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 132 (accept_3_4 37 50 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 132 2 18 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 132 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 50 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 132 2 17 25 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 132
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 50 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 132 2 16 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 50 132 (accept_3_4 31 50 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50
  132 2 15 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  50 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 50 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 132 2 14 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 132 (Polychromatic418967fa.accept_18_9_14_6_1_1790 27 50 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 132 2 13 25 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 132 (accept_3_4 25 50 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 132 2 12 25 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 132
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 50 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 132 2 11 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 50 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 132 2 10 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 132 (accept_3_4 19 50 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 132 2 9 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 132 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 50 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 132 2 8 25 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 132
  (Polychromatic418967fa.accept_19_15_12_18_1_6634 15 50 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 50 132 2 7 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 50 132 (accept_3_4 13 50 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 50 132 2 6 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 50 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 50 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 132 2 5 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 50 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 132 2 4 25 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 132 (accept_3_4 7 50 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 132 2 3 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 50 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 50
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 132 2 2 25 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 132
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 50 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 132 2 1 25 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 132 (accept_3_4 1 50 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  132)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 132 (allA_succ_of_accept 48 49 132
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 49 132 (accept_3_5 47 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  49 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 49 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 132 (accept_3_5 44 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 49 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 132
  (Polychromatic418967fa.accept_13_3_10_2_1_381 42 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 132 (accept_3_5 41 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 132 (Polychromatic418967fa.accept_16_8_1_4_1_6622 40 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 132 (accept_3_5 38 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 49 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 132
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 132 (accept_3_5 35 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 132 (Polychromatic418967fa.accept_21_12_7_6_1_3607 33 49 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 132 (accept_3_5 32 49 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 132 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 49 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 132
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 132 (accept_3_5 29 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 132 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 132 (accept_3_5 26 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 132
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 132 (accept_3_5 23 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 132 (Polychromatic418967fa.accept_14_8_7_6_1_1159 22 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 132 (accept_3_5 20 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 49 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 132
  (Polychromatic418967fa.accept_13_5_10_2_1_856 18 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 132 (accept_3_5 17 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 132 (Polychromatic418967fa.accept_14_1_7_6_1_3604 15 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 132 (accept_3_5 14 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 49 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 132
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 132 (accept_3_5 11 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 132 (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 132 (accept_3_5 8 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 49 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 132
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 6 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 132 (accept_3_5 5 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  132 (Polychromatic418967fa.accept_19_4_11_18_1_3909 4 49 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 132 (accept_3_5 2 49 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 132)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 132 (allA_succ_of_accept 47 48 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 48 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 132 2 23 24 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 48 132 3 15 16 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 48 132 4 11 12 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 48 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 132 6 7 8 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 48 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 132 4 10 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 132 3 13 16 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 132 2 19 24 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  48 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 132 12 3 4 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 132
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 48 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 132 2 17 24 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 48 132 3 11 16 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 48 132 4 8 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 48 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 132 6 5 8 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 48 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 132 4 7 12 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 48 132 3 9 16 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 48 132 2 13 24 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 48 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 132 12 2 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 48 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 132 2 11 24 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 132 3 7 16 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 132 4 5 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 19
  48 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 132 6 3 8 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 132
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 48 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 48 132 4 4 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 48 132 3 5 16 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 48 132 2 7 24 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 132 12 1 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 132 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 48 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 132 2 5 24 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 48 132 3 3 16 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 48 132 4 2 12 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 132 6 1 8 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 48 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 132 4 1 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 132 3 1 16 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 132 2 1 24 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 48 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  132)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 132 (allA_succ_of_accept 46 47 132 (accept_3_4 46 47
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 132
  (Polychromatic418967fa.accept_10_5_7_2_1_516 45 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 47 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 132 (accept_3_4 43 47 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 132 (Polychromatic418967fa.accept_20_2_7_12_1_5215 42 47 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 132
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 132 (accept_3_4 40 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 132 (Polychromatic418967fa.accept_27_11_20_24_1_6652 38 47 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 132 (accept_3_4 37 47 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 132
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 132 (accept_3_4 34 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 132 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 47 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 132 (accept_3_4 31 47 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 47 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 132
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 132 (accept_3_4 28 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 47 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 132 (accept_3_4 25 47 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 132 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 47 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 132
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 132 (accept_3_4 22 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 132 (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 47 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 132 (accept_3_4 19 47 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 47 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 132
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 132 (accept_3_4 16 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 132 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 47 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 132 (accept_3_4 13 47 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 132 (accept_3_4 10 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 132 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 47 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 132 (accept_3_4 7 47 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 132 (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 47 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 132
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 132 (accept_3_4 4 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  132 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 47 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 132 (Polychromatic418967fa.accept_19_2_9_18_1_6651 2 47 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 132 (accept_3_4 1 47 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 132))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 132 (allA_succ_of_accept 45
  46 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 46 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 46 132 2 22 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 46 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 46 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 132 2 21 23 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 132 (accept_3_5 41 46 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 132 2 20 23 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 46 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 46 132 2 19 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 46 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 46 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 132 2 18 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 132 (accept_3_5 35 46 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 132 2 17 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 46 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 132 2 16 23 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 132
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 46 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 132 2 15 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 46 132 (accept_3_5 29 46 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46
  132 2 14 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  46 132 (Polychromatic418967fa.accept_20_7_6_12_1_6650 27 46 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 46 132 2 13 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 46 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 46 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 132 2 12 23 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 132 (accept_3_5 23 46 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 132 2 11 23 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 46 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 132 2 10 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 46 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 132 2 9 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 132 (accept_3_5 17 46 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 132 2 8 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 132 (Polychromatic418967fa.accept_16_15_14_4_1_6649 15 46 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 132 2 7 23 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 132
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 46 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 46 132 2 6 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 46 132 (accept_3_5 11 46 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46
  132 2 5 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  46 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 46 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 46 132 2 4 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 46 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 46 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 132 2 3 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 132 (accept_3_5 5 46 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 132 2 2 23 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 46 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 46 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 132 2 1 23 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 132
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 46 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 132)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 132 (allA_succ_of_accept 44 45 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 45 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 132 (Polychromatic418967fa.accept_10_3_5_2_1_38 43 45 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 132 3 14 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 41
  45 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 132
  (Polychromatic418967fa.accept_13_1_6_2_1_377 40 45 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 132 3 13 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 132 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 45 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 45 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 132 3 12 15 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 132
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 45 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 132 (Polychromatic418967fa.accept_13_8_6_2_1_865 34 45 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 132 3 11 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 32
  45 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 132
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 31 45 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 132 3 10 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 132 (Polychromatic418967fa.accept_17_12_11_13_1_5378 29 45 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 132 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 45 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 132 3 9 15 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 132
  (Polychromatic418967fa.accept_18_8_9_6_1_3989 26 45 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 45 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 132 3 8 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 45 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 132
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 22 45 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 132 3 7 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 132 (Polychromatic418967fa.accept_18_2_9_6_1_4025 20 45 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 132 (Polychromatic418967fa.accept_18_1_9_6_1_6630 19 45 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 132 3 6 15 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 132
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 45 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 45 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 132 3 5 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 132 (Polychromatic418967fa.accept_13_1_6_2_1_377 14 45 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 132
  (Polychromatic418967fa.accept_10_3_5_2_1_38 13 45 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 132 3 4 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 45 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 132 (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 45
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 132 3 3 15 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 132
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 45 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 132 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 45 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 132 3 2 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 132 (Polychromatic418967fa.accept_21_5_3_6_1_6648 5 45 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 132
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 45 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 132 3 1 15 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 45 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 45 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  132))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 132 (allA_succ_of_accept 43 44 132 (accept_3_4 43 44
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 132 2 21 22 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 132
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 44 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 132 4 10 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 44 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 132 2 19 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 132 (accept_3_4 37 44 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 132 4 9 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 44 132 (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 44 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 132 2 17 22 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 44 132 11 3 4 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 44 132 4 8 11 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 132 (accept_3_4 31 44 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 132 2 15 22 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 44 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 44 132 4 7 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 44 132 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 44 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 132 2 13 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 132 (accept_3_4 25 44 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 132 4 6 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 44 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 44 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 132 22 1 2 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 132
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 132 4 5 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 132 (accept_3_4 19 44 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  132 2 9 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 44 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 132 4 4 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 44 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 132 2 7 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 132 (accept_3_4 13 44 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 132 4 3 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 11 44 132 11 1 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 44 132 2 5 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 44 132 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 44 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 132 4 2 11 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 132 (accept_3_4 7 44 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 132 2 3 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 44 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 132 4 1 11 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 44 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 132 2 1 22 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 132 (accept_3_4 1 44 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  132)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 132 (allA_succ_of_accept 42 43 132
  (Polychromatic418967fa.accept_19_4_5_18_1_6647 42 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 132 (accept_3_5 41 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 43 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 132 (accept_3_5 38 43 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 43 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 132
  (Polychromatic418967fa.accept_19_17_5_18_1_6646 36 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 132 (accept_3_5 35 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 132 (Polychromatic418967fa.accept_27_7_16_24_1_6645 34 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 43 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 132 (accept_3_5 32 43 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 43 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 132
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 132 (accept_3_5 29 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 132 (Polychromatic418967fa.accept_17_10_9_13_1_6644 27 43 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 132 (accept_3_5 26 43 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 132 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 43 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 132
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 132 (accept_3_5 23 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 43 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 132 (accept_3_5 20 43 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 43 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 132
  (Polychromatic418967fa.accept_13_5_4_2_1_846 18 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 132 (accept_3_5 17 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 43 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 132 (accept_3_5 14 43 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 43 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 132
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 132 (accept_3_5 11 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 43 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 132 (accept_3_5 8 43 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 43 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 132
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 132 (accept_3_5 5 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  132 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 43 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 43 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 132 (accept_3_5 2 43 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 43 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 132))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 132
  (allA_succ_of_accept 41 42 132 (Polychromatic418967fa.accept_19_3_4_18_1_3882 41 42 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 132 2 20 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 42 132 3 13 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 42 132 2 19 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 132 (Polychromatic418967fa.accept_13_11_3_2_1_863
  37 42 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 132 6 6 7 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 132
  (Polychromatic418967fa.accept_13_9_3_2_1_399 35 42 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 42 132 2 17 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 42 132 3 11 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 42 132 2 16 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 132 (Polychromatic418967fa.accept_13_5_3_2_1_1499 31 42 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 132 6 5 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 132 (Polychromatic418967fa.accept_20_9_2_12_1_5144 29 42 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 132 2 14 21 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 132 3 9 14 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 132 2 13 21 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 132
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 25 42 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 132 6 4 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 132 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 42 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 132 2 11 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 132 3 7 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 132 2 10 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 132 (Polychromatic418967fa.accept_20_19_2_12_1_2516
  19 42 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 132 6 3 7 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 132
  (Polychromatic418967fa.accept_19_17_4_18_1_6643 17 42 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 132 2 8 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 42 132 3 5 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 132 2 7 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 132 (Polychromatic418967fa.accept_23_13_19_17_1_4984 13 42 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 132 6 2 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 132 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 42 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 132 2 5 21 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 132 3 3 14 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 132 2 4 21 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 132
  (Polychromatic418967fa.accept_20_7_2_12_1_6642 7 42 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 132 6 1 7 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 132 (Polychromatic418967fa.accept_13_5_3_2_1_1499 5 42 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 132 2 2 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 132 3 1 14 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 132 2 1 21 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 132 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 42 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  132)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 132 (allA_succ_of_accept 40 41 132 (accept_3_4 40 41 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 39
  41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 132
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 132 (accept_3_4 37 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 132 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 132 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 41 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 132 (accept_3_4 34 41 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 132 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 41 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 132
  (Polychromatic418967fa.accept_21_11_20_6_1_6641 32 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 132 (accept_3_4 31 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 41 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 132 (accept_3_4 28 41 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 132 (Polychromatic418967fa.accept_16_11_9_4_1_5438 27 41 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 132
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 132 (accept_3_4 25 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 132 (Polychromatic418967fa.accept_16_8_9_4_1_630 24 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 132 (Polychromatic418967fa.accept_10_3_1_2_1_521 23 41 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 132 (accept_3_4 22 41 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 41 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 132
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 132 (accept_3_4 19 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 132 (Polychromatic418967fa.accept_21_18_20_6_1_6640 18 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 132 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 41 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 132 (accept_3_4 16 41 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 132 (Polychromatic418967fa.accept_18_15_5_6_1_5293 15 41 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 132
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 41 132 (accept_3_4 13 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 41 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 41 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 41 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 132 (accept_3_4 10 41 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 132 (Polychromatic418967fa.accept_10_9_1_2_1_522 9
  41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 132
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 132 (accept_3_4 7 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  132 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 41 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 132 (accept_3_4 4 41 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 41 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  41 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 132 (accept_3_4 1 41 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 132))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 132
  (allA_succ_of_accept 39 40 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 40 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 132 2 19 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 40
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 132 4 9 10 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 132 (accept_3_5 35
  40 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 132 2 17 20 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 132
  (Polychromatic418967fa.accept_16_1_8_4_1_4334 33 40 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 40 132 4 8 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 40 132 (Polychromatic418967fa.accept_16_15_8_4_1_1355 31 40 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 132 2 15 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 132 (accept_3_5 29 40 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 132 4 7 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 40 132 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 40 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 132 2 13 20 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 40 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 40 132 4 6 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 40 132 (accept_3_5 23 40 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40
  132 2 11 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  40 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 40 132 4 5 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 40 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 40 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 132 2 9 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 132 (accept_3_5 17 40 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 132 4 4 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 40 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 40 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 132 2 7 20 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 132
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 40 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 40 132 4 3 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 40 132 (accept_3_5 11 40 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  132 2 5 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  40 132 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 40 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 40 132 4 2 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 40 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 40 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 132 2 3 20 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 132 (accept_3_5 5 40 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 132 4 1 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 40 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 40 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 132 2 1 20 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 132
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 40 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 132)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 132 (allA_succ_of_accept 38 39 132
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 39 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 39 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 132 3 12 13 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 35
  39 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 39 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 132 3 11 13 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 39 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 132 3 10 13 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 39 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 132 3 9 13 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 39 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 39 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 132 3 8 13 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 39 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 39 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 132 3 7 13 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 39 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 39 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 132 3 6 13 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 39 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 39 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 132 3 5 13 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 39 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 39 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 132 3 4 13 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 132
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 39 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 39 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 132 3 3 13 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 39 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 132 3 2 13 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 39 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 132 3 1 13 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 39 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 39 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 132))))))))))))))))))))))))))))))))))))))) (allB_succ 38 132
  (allA_succ_of_accept 37 38 132 (accept_3_4 37 38 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  132 2 18 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 38 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 132 2 17 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 132 (Polychromatic418967fa.accept_15_3_8_12_1_900 33 38 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 132 2 16 19 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 132 (accept_3_4 31 38 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 132 2 15 19 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 132
  (Polychromatic418967fa.accept_13_3_12_2_1_385 29 38 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 132 2 14 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 132 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 38 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 132 2 13 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 132 (accept_3_4 25 38 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 132 2 12 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 38 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 132 2 11 19 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 132
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 38 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 132 2 10 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 132 (accept_3_4 19 38 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  132 2 9 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 38 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 132 2 8 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 132 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 38 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 132 2 7 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 132 (accept_3_4 13 38 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 132 2 6 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 38 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 132 2 5 19 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 38 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 132 2 4 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 132 (accept_3_4 7 38 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 132
  2 3 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  132 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 38 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 132 2 2 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 38 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 132 2 1 19 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 132 (accept_3_4 1 38 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 132)))))))))))))))))))))))))))))))))))))) (allB_succ 37 132 (allA_succ_of_accept 36 37 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 132 (accept_3_5 35 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 37 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 132 (accept_3_5 32 37 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 37 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 132 (accept_3_5 29 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 132 (Polychromatic418967fa.accept_16_12_5_4_1_3275 28 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 132 (Polychromatic418967fa.accept_17_10_3_13_1_6639 27 37 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 132 (accept_3_5 26 37 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 37 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 132 (accept_3_5 23 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 37 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 132 (accept_3_5 20 37 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 132 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 37 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 132
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 132 (accept_3_5 17 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 37 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 132 (accept_3_5 14 37 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 37 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 132 (accept_3_5 11 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 37 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 132 (accept_3_5 8 37 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 37 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 132
  (Polychromatic418967fa.accept_15_6_7_12_1_869 6 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 132 (accept_3_5 5 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  132 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 37 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 37 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 132 (accept_3_5 2 37 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 132))))))))))))))))))))))))))))))))))))) (allB_succ 36 132
  (allA_succ_of_accept 35 36 132 (Polychromatic418967fa.accept_14_7_8_6_1_1164 35 36 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 132 2 17 18 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 132 3 11 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 132 4 8 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 132 (Polychromatic418967fa.accept_10_1_6_2_1_867 31
  36 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 132 6 5 6 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 132
  (Polychromatic418967fa.accept_13_3_10_2_1_381 29 36 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 36 132 4 7 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 36 132 3 9 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 36 132 2 13 18 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 132 (Polychromatic418967fa.accept_13_12_10_2_1_1451 25 36 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 132 12 2 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 132 2 11 18 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 132 3 7 12 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 132 4 5 9 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 132
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 36 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 132 6 3 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 132 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 36 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 132 4 4 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 132 3 5 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 132 2 7 18 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 132 (Polychromatic418967fa.accept_19_13_17_18_1_6638 13 36
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 132 12 1 3 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 132
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 36 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 36 132 2 5 18 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 36 132 3 3 12 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 36 132 4 2 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 132 (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 36 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 132 6 1 6 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 132 4 1 9 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 132 3 1 12 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 132 2 1 18 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 132
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 36 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 132)))))))))))))))))))))))))))))))))))) (allB_succ 35 132 (allA_succ_of_accept 34 35 132 (accept_3_4 34
  35 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 132
  (Polychromatic418967fa.accept_10_3_5_2_1_38 33 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 35 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 132 (accept_3_4 31 35 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 35 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 29
  35 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 132 (accept_3_4 28 35
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 132
  (Polychromatic418967fa.accept_10_7_5_2_1_880 27 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 132 (Polychromatic418967fa.accept_20_6_15_12_1_6637 26 35 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 132 (accept_3_4 25 35 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 132 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 35 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 132
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 132 (accept_3_4 22 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 35 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 132 (accept_3_4 19 35 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 132 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 35 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 132
  (Polychromatic418967fa.accept_10_7_5_2_1_880 17 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 132 (accept_3_4 16 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 35 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 132 (accept_3_4 13 35 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 35 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 132
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 132 (accept_3_4 10 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 132 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 132 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 35 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 132 (accept_3_4 7 35 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 132 (Polychromatic418967fa.accept_13_6_9_2_1_838 6 35 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 132
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 132 (accept_3_4 4 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  132 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 35 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 132 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 35 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 132 (accept_3_4 1 35 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 132))))))))))))))))))))))))))))))))))) (allB_succ 34 132 (allA_succ_of_accept 33 34 132
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 34 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 132 2 16 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 34 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 132 2 15 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 132 (accept_3_5 29 34 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 132 2 14 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 132 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 34 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 132 2 13 17 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 132
  (Polychromatic418967fa.accept_21_4_13_6_1_6618 25 34 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 132 2 12 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 132 (accept_3_5 23 34 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  132 2 11 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 34 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 132 2 10 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 34 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 132 2 9 17 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 132 (accept_3_5 17 34 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 132 2 8 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 132 (Polychromatic418967fa.accept_18_15_16_6_1_1751 15 34
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 132 2 7 17 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 132
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 34 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 132 2 6 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 132 (accept_3_5 11 34 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  132 2 5 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 132 (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 34 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 132 2 4 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 132 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 34 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 132 2 3 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 132 (accept_3_5 5 34 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 132 2 2 17 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 132 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 34 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 132 2 1 17 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 132
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 34 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 132)))))))))))))))))))))))))))))))))) (allB_succ 33 132 (allA_succ_of_accept 32 33 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 33 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 132 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 33 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 132 3 10 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 29
  33 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 132
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 33 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 33 132 3 9 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 33 132 (Polychromatic418967fa.accept_17_9_16_13_1_6636 26 33 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 33 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 132 3 8 11 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 132
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 33 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 33 132 11 2 3 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 33 132 3 7 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 132 (Polychromatic418967fa.accept_17_3_16_13_1_6635 20 33 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 132 (Polychromatic418967fa.accept_16_3_1_4_1_5426 19 33 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 132 3 6 11 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 132
  (Polychromatic418967fa.accept_15_2_3_12_1_891 17 33 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 132 (Polychromatic418967fa.accept_18_16_15_6_1_4039 16 33 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 132 3 5 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 132 (Polychromatic418967fa.accept_16_14_1_4_1_5432 14 33 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 132
  (Polychromatic418967fa.accept_8_5_1_4_1_628 13 33 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 132 3 4 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 11 33 132 11 1 3 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 33 132 (Polychromatic418967fa.accept_18_10_15_6_1_6621 10 33 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 132 3 3 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 33 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 132
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 33 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 33 132 3 2 11 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 33 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 33 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 33 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 132 3 1 11 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 132
  (Polychromatic418967fa.accept_15_2_3_12_1_891 2 33 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 33 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 33 132))))))))))))))))))))))))))))))))) (allB_succ 32 132
  (allA_succ_of_accept 31 32 132 (accept_3_4 31 32 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  132 2 15 16 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  32 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 32 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 132 4 7 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 132 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 32 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 132 2 13 16 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 132 (accept_3_4 25 32 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 132 4 6 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 32 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 132 2 11 16 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 132
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 132 4 5 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 132 (accept_3_4 19 32 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  132 2 9 16 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 32 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 132 4 4 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 132 (Polychromatic418967fa.accept_21_15_11_6_1_5121 15 32 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 132 2 7 16 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 132 (accept_3_4 13 32 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 132 4 3 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 32 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 32 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 132 2 5 16 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 32 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 132 4 2 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 132 (accept_3_4 7 32 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 132
  2 3 16 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  132 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 32 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 132 4 1 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 32 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 132 2 1 16 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 132 (accept_3_4 1 32 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 132)))))))))))))))))))))))))))))))) (allB_succ 31 132 (allA_succ_of_accept 30 31 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 132 (accept_3_5 29 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 31 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 132 (accept_3_5 26 31 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 31 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 132
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 132 (accept_3_5 23 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 132 (Polychromatic418967fa.accept_13_9_5_2_1_2185 22 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 31 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 132 (accept_3_5 20 31 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 31 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 132
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 132 (accept_3_5 17 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 132 (Polychromatic418967fa.accept_19_15_12_18_1_6634 15 31 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 132 (accept_3_5 14 31 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 132 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 31 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 132
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 132 (accept_3_5 11 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 31 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 132 (accept_3_5 8 31 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 132
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 132 (accept_3_5 5 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  132 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 31 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 31 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 132 (accept_3_5 2 31 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 31 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 132))))))))))))))))))))))))))))))) (allB_succ 30 132
  (allA_succ_of_accept 29 30 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 30 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 132 2 14 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 132 3 9 10 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 132 2 13 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 25
  30 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 132 6 4 5 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 132
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 30 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 132 2 11 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 30 132 3 7 10 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 30 132 2 10 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 30 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 132 6 3 5 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 30 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 132 2 8 15 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 132 3 5 10 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 132 2 7 15 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 132
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 30 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 132 6 2 5 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 30 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 132 2 5 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 132 3 3 10 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 30 132 2 4 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 30 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 132 6 1 5 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 132
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 30 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 132 2 2 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 30 132 3 1 10 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 30 132 2 1 15 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 30 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 132)))))))))))))))))))))))))))))) (allB_succ 29 132 (allA_succ_of_accept
  28 29 132 (accept_3_4 28 29 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 132
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 29 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 29 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 132 (accept_3_4 25 29 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 132 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 29 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 23
  29 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 132 (accept_3_4 22 29
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 132
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 132 (Polychromatic418967fa.accept_24_20_5_12_1_6633 20 29 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 132 (accept_3_4 19 29 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 132 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 29 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 17
  29 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 132 (accept_3_4 16 29
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 132
  (Polychromatic418967fa.accept_18_15_11_6_1_4067 15 29 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 132 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 29 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 132 (accept_3_4 13 29 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 132 (Polychromatic418967fa.accept_10_1_9_2_1_45 11
  29 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 132 (accept_3_4 10 29
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 132 (Polychromatic418967fa.accept_7_2_1_6_1_173
  9 29 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 132
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 29 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 132 (accept_3_4 7 29 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  132 (Polychromatic418967fa.accept_16_6_13_4_1_643 6 29 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 29 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 132 (accept_3_4 4 29 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 29 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 132
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 29 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 132 (accept_3_4 1 29 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  132))))))))))))))))))))))))))))) (allB_succ 28 132 (allA_succ_of_accept 27 28 132
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 27 28 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 132 2 13 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 28 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 132 4 6 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 132 (accept_3_5 23 28 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 28 132 2 11 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 28 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 28 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 132 4 5 7 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 132
  (Polychromatic418967fa.accept_16_3_12_4_1_170 19 28 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 132 2 9 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 132 (accept_3_5 17 28 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  132 4 4 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 132 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 28 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 132 2 7 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 28 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 28 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 132 4 3 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 132 (accept_3_5 11 28 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 132 2 5 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 28 132 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 28 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 132 4 2 7 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 132
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 28 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 28 132 2 3 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 132 (accept_3_5 5 28 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 132
  4 1 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 132 2 1 14 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 132 (Polychromatic418967fa.accept_15_1_13_12_1_347 1 28 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 132)))))))))))))))))))))))))))) (allB_succ 27 132 (allA_succ_of_accept 26
  27 132 (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 27 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 132 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 27 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 132 3 8 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 23
  27 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 132
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 22 27 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 132 3 7 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 132 (Polychromatic418967fa.accept_17_3_10_13_1_2021 20 27 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 132 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 27 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 132 3 6 9 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 132
  (Polychromatic418967fa.accept_20_17_7_12_1_6632 17 27 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 132 (Polychromatic418967fa.accept_13_3_1_2_1_2960 16 27 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 132 3 5 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 132 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 27 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 132
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 13 27 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 132 3 4 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 132 (Polychromatic418967fa.accept_19_11_8_18_1_6631 11 27 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 132 (Polychromatic418967fa.accept_19_10_8_18_1_2669 10 27
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 132 3 3 9 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 132
  (Polychromatic418967fa.accept_16_8_11_4_1_3290 8 27 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 27 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 132 3 2 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 132 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 27 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 132
  (Polychromatic418967fa.accept_10_4_7_2_1_211 4 27 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 132 3 1 9 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 132 (Polychromatic418967fa.accept_18_2_9_6_1_4025 2 27 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 132 (Polychromatic418967fa.accept_18_1_9_6_1_6630 1 27 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 132))))))))))))))))))))))))))) (allB_succ 26
  132 (allA_succ_of_accept 25 26 132 (accept_3_4 25 26 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24
  26 132 2 12 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 26 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 26 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 132 2 11 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 26 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 132 2 10 13 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 132 (accept_3_4 19 26 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 132 2 9 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 132 (Polychromatic418967fa.accept_19_17_7_18_1_6629
  17 26 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 132 2 8 13 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 132
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 26 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 132 2 7 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 132 (accept_3_4 13 26 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  132 2 6 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 26 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 132 2 5 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 132 (Polychromatic418967fa.accept_18_9_8_6_1_4021 9 26 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 132 2 4 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 132 (accept_3_4 7 26 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 132 2 3 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 132 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 26 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 132 2 2 13 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 132
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 26 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 132 2 1 13 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 132 (accept_3_4 1 26 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  132)))))))))))))))))))))))))) (allB_succ 25 132 (allA_succ_of_accept 24 25 132
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 25 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 132 (accept_3_5 23 25 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 132 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 25 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 25 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 132 (accept_3_5 20 25 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 25 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 132
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 25 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 132 (accept_3_5 17 25 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 25 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 132 (Polychromatic418967fa.accept_17_15_8_13_1_6628 15 25 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 132 (accept_3_5 14 25 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 25 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 132
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 132 (accept_3_5 11 25 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 25 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 132 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 25 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 132 (accept_3_5 8 25 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 132 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 25 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 132
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 25 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 132 (accept_3_5 5 25 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  132 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 25 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 25 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 132 (accept_3_5 2 25 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 25 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 132))))))))))))))))))))))))) (allB_succ 24 132
  (allA_succ_of_accept 23 24 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 132 2 11 12 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 132 3 7 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 132 4 5 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 132 (Polychromatic418967fa.accept_15_4_9_12_1_2495
  19 24 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 132 6 3 4 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 132
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 24 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 132 4 4 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 132 3 5 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 132 2 7 12 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 132 (Polychromatic418967fa.accept_16_13_8_4_1_3250 13 24 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 132 12 1 2 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 132 2 5 12 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 132 3 3 8 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 132 4 2 6 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 132
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 24 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 132 6 1 4 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 132 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 24 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 132 4 1 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 132 3 1 8 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 132 2 1 12 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 132 (Polychromatic418967fa.accept_16_1_8_4_1_4334 1 24 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 132)))))))))))))))))))))))) (allB_succ 23
  132 (allA_succ_of_accept 22 23 132 (accept_3_4 22 23 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 23 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 23 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 23 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 132 (accept_3_4 19 23 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 132 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 23 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 132
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 23 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 132 (accept_3_4 16 23 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 23 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 132 (Polychromatic418967fa.accept_16_14_7_4_1_3243 14 23 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 132 (accept_3_4 13 23 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 23 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 132
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 132 (accept_3_4 10 23 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 132 (Polychromatic418967fa.accept_20_9_3_12_1_6627 9 23 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 23 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 132 (accept_3_4 7 23 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 132 (Polychromatic418967fa.accept_13_6_10_2_1_1449 6 23 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 132
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 23 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 132 (accept_3_4 4 23 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  132 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 23 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 132 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 23 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 132 (accept_3_4 1 23 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 132))))))))))))))))))))))) (allB_succ 22 132 (allA_succ_of_accept 21 22 132
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 22 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 132 2 10 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 22 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 132 2 9 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 132 (accept_3_5 17 22 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 132 2 8 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 132 (Polychromatic418967fa.accept_17_15_5_13_1_6626 15 22 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 132 2 7 11 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 132
  (Polychromatic418967fa.accept_16_13_6_4_1_3277 13 22 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 22 132 2 6 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 11 22 132 11 1 2 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 10 22 132 2 5 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 22 132 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 22 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 132 2 4 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 22 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 132 2 3 11 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 132 (accept_3_5 5 22 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 132 2 2 11 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 22
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 132 2 1 11 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 132
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 22 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 132)))))))))))))))))))))) (allB_succ 21 132 (allA_succ_of_accept 20 21 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 21 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 132 3 6 7 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 21 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 21 132 3 5 7 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 21 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 21 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 132 3 4 7 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 21 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 21 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 132 3 3 7 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 132 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 132
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 21 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 21 132 3 2 7 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 21 132 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 132 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 132 3 1 7 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 132
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 21 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 21 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 21 132))))))))))))))))))))) (allB_succ 20 132 (allA_succ_of_accept 19 20 132
  (accept_3_4 19 20 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 132 2 9 10 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 132
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 20 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 132 4 4 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 132 (Polychromatic418967fa.accept_21_15_20_6_1_6625 15 20 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 132 2 7 10 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 132 (accept_3_4 13 20 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 132 4 3 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 132 (Polychromatic418967fa.accept_19_11_1_18_1_5276 11 20 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 132 2 5 10 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 132
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 20 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 132 4 2 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 132 (accept_3_4 7 20 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 132
  2 3 10 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  132 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 20 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 132 4 1 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 132 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 20 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 132 2 1 10 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 132 (accept_3_4 1 20 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 132)))))))))))))))))))) (allB_succ 19 132 (allA_succ_of_accept 18 19 132
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 19 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 132 (accept_3_5 17 19 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 132 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 19 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 19 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 132 (accept_3_5 14 19 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 132 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 19 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 19 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 132 (accept_3_5 11 19 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 132 (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 19 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 132 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 19 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 132 (accept_3_5 8 19 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 132 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 19 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 132
  (Polychromatic418967fa.accept_16_6_3_4_1_6624 6 19 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 132 (accept_3_5 5 19 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  132 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 19 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 132 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 19 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 132 (accept_3_5 2 19 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 19 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 132))))))))))))))))))) (allB_succ 18 132 (allA_succ_of_accept 17
  18 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 18 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 18 132 2 8 9 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 18 132 3 5 6 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 18 132 2 7 9 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 132 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 18 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 132 6 2 3 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 132
  (Polychromatic418967fa.accept_21_11_18_6_1_3521 11 18 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 18 132 2 5 9 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 18 132 3 3 6 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 18 132 2 4 9 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 18 132 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 18 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 132 6 1 3 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 18 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 132 2 2 9 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 132 3 1 6 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 132 2 1 9 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 132
  (Polychromatic418967fa.accept_23_1_18_17_1_6623 1 18 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 132)))))))))))))))))) (allB_succ 17 132 (allA_succ_of_accept 16 17 132 (accept_3_4 16 17 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 132 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 17 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 132
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 17 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 132 (accept_3_4 13 17 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 17 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 132 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 17 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 132 (accept_3_4 10 17 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 17 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 132
  (Polychromatic418967fa.accept_16_8_1_4_1_6622 8 17 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 132 (accept_3_4 7 17 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  132 (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 17 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 17 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 132 (accept_3_4 4 17 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 17 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 132
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 17 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 132 (accept_3_4 1 17 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  132))))))))))))))))) (allB_succ 16 132 (allA_succ_of_accept 15 16 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 16
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 16 132 2 7 8 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 16 132
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 16 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 16 132 4 3 4 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 16 132 (accept_3_5 11 16 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 16
  132 2 5 8 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 16
  132 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 16 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 16 132 4 2 4 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 16 132 (Polychromatic418967fa.accept_21_7_16_6_1_3516 7 16 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 132 2 3 8 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 132 (accept_3_5 5 16 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 16 132 4 1 4 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 16 132 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 16 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 132 2 1 8 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 16
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 132)))))))))))))))) (allB_succ 15 132
  (allA_succ_of_accept 14 15 132 (Polychromatic418967fa.accept_16_14_15_4_1_3268 14 15 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 132 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 15 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 132 3 4 5 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 132
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 15 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 132 (Polychromatic418967fa.accept_18_10_15_6_1_6621 10 15 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 132 3 3 5 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 132 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 15 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 132
  (Polychromatic418967fa.accept_10_7_5_2_1_880 7 15 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 132 3 2 5 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 132 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 15 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 132 (Polychromatic418967fa.accept_18_4_15_6_1_3994 4 15 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 132 3 1 5 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 132
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 15 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 132 (Polychromatic418967fa.accept_21_1_15_6_1_6620 1 15 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 132))))))))))))))) (allB_succ 14 132 (allA_succ_of_accept 13 14 132
  (accept_3_4 13 14 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 132 2 6 7 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 132
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 14 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 132 2 5 7 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 132 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 14 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 132 2 4 7 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 132 (accept_3_4 7 14 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 132 2 3 7 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 132 (Polychromatic418967fa.accept_23_5_14_17_1_6619 5 14 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 132 2 2 7 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 132 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 14
  132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 132 2 1 7 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 132 (accept_3_4 1 14
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 132)))))))))))))) (allB_succ 13 132 (allA_succ_of_accept 12
  13 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 13 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 132 (accept_3_5 11 13 132 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 13 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 13 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 132 (accept_3_5 8 13 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 132 (Polychromatic418967fa.accept_9_7_4_6_1_273 7
  13 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 132
  (Polychromatic418967fa.accept_16_6_13_4_1_643 6 13 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 132 (accept_3_5 5 13 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  132 (Polychromatic418967fa.accept_21_4_13_6_1_6618 4 13 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 132 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 13 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 132 (accept_3_5 2 13 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 132 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 13 132 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 132))))))))))))) (allB_succ 12 132
  (allA_succ_of_accept 11 12 132 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 132 2 5 6 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 12 132 3 3 4 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 12 132 4 2 3 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 132 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 132 6 1 2 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 132
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 132 4 1 3 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 12 132 3 1 4 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 12 132 2 1 6 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 132 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 132)))))))))))) (allB_succ 11 132 (allA_succ_of_accept 10 11 132
  (accept_3_4 10 11 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 11 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 132 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 11 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 132 (accept_3_4 7 11 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 132 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 11 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 132 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  11 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 132 (accept_3_4 4 11 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  11 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 132
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 11 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 132 (accept_3_4 1 11 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  132))))))))))) (allB_succ 10 132 (allA_succ_of_accept 9 10 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 10 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 132 2 4 5 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 132
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 10 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 132 2 3 5 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 132 (accept_3_5 5 10 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 132
  2 2 5 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 132
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 10 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 132 2 1 5 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 132 (Polychromatic418967fa.accept_25_1_10_7_1_6617 1 10 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 132)))))))))) (allB_succ 9 132 (allA_succ_of_accept 8 9 132
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 9 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 132 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 9 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 132 3 2 3 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 132 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 9 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 132
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 9 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 132 3 1 3 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 132 (Polychromatic418967fa.accept_18_2_9_6_1_4025 2 9 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 132 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 9 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 132))))))))) (allB_succ 8 132
  (allA_succ_of_accept 7 8 132 (accept_3_4 7 8 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 132 2
  3 4 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 132
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 8 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 132 4 1 2 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 132 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 8 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 132 2 1 4 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 132 (accept_3_4 1 8 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 132)))))))) (allB_succ 7 132 (allA_succ_of_accept 6 7 132
  (Polychromatic418967fa.accept_15_6_7_12_1_869 6 7 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 132 (accept_3_5 5 7 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 132
  (Polychromatic418967fa.accept_9_4_7_6_1_255 4 7 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 132 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 7 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 132 (accept_3_5 2 7 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 132 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 7 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 132))))))) (allB_succ 6 132 (allA_succ_of_accept 5 6 132
  (Polychromatic418967fa.accept_15_5_6_12_1_916 5 6 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 132 2 2 3 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 6 132 3 1 2 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 6 132 2 1 3 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 132 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 6 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 132)))))) (allB_succ 5 132 (allA_succ_of_accept 4 5 132 (accept_3_4 4 5
  132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 132 (Polychromatic418967fa.accept_9_3_5_6_1_253
  3 5 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 132
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 5 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 132 (accept_3_4 1 5 132 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 132)))))
  (allB_succ 4 132 (allA_succ_of_accept 3 4 132 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 4 132 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 132 2 1 2 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 132 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 4 132
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 132)))) (allB_succ 3 132 (allA_succ_of_accept
  2 3 132 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 3 132 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 132 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 3 132 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 132))) (allB_succ 2 132 (allA_succ_of_accept 1 2 132 (accept_3_4 1 2 132
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 132)) (allB_two
  132))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


