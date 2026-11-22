-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch139
-- name    : Polychromatic418967fa_Branch139
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:13:53.265142+00:00
-- url     : https://prove2.me/theorems/0ed40259-ad7d-41dc-ba06-eca78d0ca3e8
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

def Polychromatic418967fa.branch_139 : allB 139 139 :=
  allB_succ' 2 138 139 (Eq.refl Bool.true) (allA_succ_of_accept 1 138 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  138 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 139)) (allB_succ' 3 137 139
  (Eq.refl Bool.true) (allA_of_3_1 3 137 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 136 139 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 136 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 139 (accept_3_3 2 136 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 139 (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 136 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 139)))) (allB_succ' 5 135 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 135 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 135 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 139 (accept_3_3 2 135 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 1
  135 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 139))))) (allB_succ' 6 134 139
  (Eq.refl Bool.true) (allA_of_3_1 6 134 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 133 139 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 133 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 139 (accept_3_3 5 133 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 139 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 133 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 139
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 133 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 139 (accept_3_3 2 133 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 133 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 139))))))) (allB_succ' 8 132 139 (Eq.refl Bool.true) (allA_succ_of_accept 7 132 139
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 132 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 132 139 (Polychromatic418967fa.accept_13_6_2_9_1_1188 6 132 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 132 139 (accept_3_3 5 132 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 132 139 (Polychromatic418967fa.accept_17_4_13_3_1_7166 4 132 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 132 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 132 139 (accept_3_3 2 132 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  132 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 132 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 132 139)))))))) (allB_succ' 9 131 139 (Eq.refl Bool.true) (allA_of_3_1 9 131 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 130 139 (Eq.refl Bool.true) (allA_succ_of_accept 9 130 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 130 139 (accept_3_3 8 130 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  130 139 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 130 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 130 139 (Polychromatic418967fa.accept_15_6_10_4_1_150 6 130 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 130 139 (accept_3_3 5 130 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 130 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 130 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 130 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 130 139 (accept_3_3 2 130 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  130 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 130 139)))))))))) (allB_succ' 11 129 139 (Eq.refl Bool.true) (allA_succ_of_accept 10 129 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 129 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 129 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 139 (accept_3_3 8 129 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 129 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 129 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  129 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 139 (accept_3_3 5 129
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 139 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 129 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 139
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 129 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 139 (accept_3_3 2 129 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 129 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129 139))))))))))) (allB_succ' 12 128 139 (Eq.refl Bool.true) (allA_of_3_1 12 128 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 127 139 (Eq.refl Bool.true) (allA_succ_of_accept 12 127 139
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 139 (accept_3_3 11 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 139 (Polychromatic418967fa.accept_15_10_7_4_1_1222 10 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 127 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 139 (accept_3_3 8 127 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 127 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 139
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 139 (accept_3_3 5 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 127 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 139 (accept_3_3 2 127 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 139 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 127 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 139))))))))))))) (allB_succ' 14 126 139 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 126 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 139
  (Polychromatic418967fa.accept_17_12_7_3_1_1498 12 126 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 126 139 (accept_3_3 11 126 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 126 139 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 126 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 126 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 139 (accept_3_3 8 126 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 139 (Polychromatic418967fa.accept_20_7_6_19_1_2949 7 126 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 126 139
  (Polychromatic418967fa.accept_23_6_11_1_1_7202 6 126 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 126 139 (accept_3_3 5 126 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  126 139 (Polychromatic418967fa.accept_17_4_7_3_1_1417 4 126 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 126 139 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 126 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 139 (accept_3_3 2 126 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 139)))))))))))))) (allB_succ' 15 125 139 (Eq.refl
  Bool.true) (allA_of_3_1 15 125 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 124 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 124 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 124 139 (accept_3_3 14 124 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 124 139 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 124 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 12
  124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 139 (accept_3_3 11
  124 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 139
  (Polychromatic418967fa.accept_9_1_7_4_1_52 10 124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 124 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 139 (accept_3_3 8 124 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 124 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 124 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 6
  124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 139 (accept_3_3 5 124
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 139
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 124 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 139 (accept_3_3 2 124 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 124 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 124 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 139)))))))))))))))) (allB_succ' 17 123 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 123 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 123 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 139 (Polychromatic418967fa.accept_13_2_6_9_1_2636 15 123
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 139 (accept_3_3 14 123
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 139
  (Polychromatic418967fa.accept_17_13_4_3_1_1446 13 123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 123 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 123 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 139 (accept_3_3 11 123 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 123 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 123 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 9
  123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 139 (accept_3_3 8 123
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 139
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 123 139 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 123 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 139 (accept_3_3 5 123 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 123 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 139 (accept_3_3 2 123
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 139 (Polychromatic418967fa.accept_9_1_6_4_1_49
  1 123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 139))))))))))))))))) (allB_succ'
  18 122 139 (Eq.refl Bool.true) (allA_of_3_1 18 122 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 121 139
  (Eq.refl Bool.true) (allA_succ_of_accept 18 121 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 139 (accept_3_3 17 121 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 139 (Polychromatic418967fa.accept_19_16_7_6_1_7201 16 121
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 139
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 139 (accept_3_3 14 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 139 (Polychromatic418967fa.accept_19_13_7_6_1_5826 13 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 139 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 121 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 139 (accept_3_3 11 121 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 139
  (Polychromatic418967fa.accept_21_9_16_13_1_1541 9 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 139 (accept_3_3 8 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 139 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 139 (accept_3_3 5 121 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 121 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 139
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 139 (accept_3_3 2 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 139))))))))))))))))))) (allB_succ' 20 120 139 (Eq.refl Bool.true) (allA_succ_of_accept 19
  120 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 120 139 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 120 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 139 (accept_3_3 17 120 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 120 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 120 139 (accept_3_3 14 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 120 139 (Polychromatic418967fa.accept_16_13_8_11_1_4785 13 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 120 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 120 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 139 (accept_3_3 11 120 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 120 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 139
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 120 139 (accept_3_3 8 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  120 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 120 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 120 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 139 (accept_3_3 5 120 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 139 (Polychromatic418967fa.accept_16_4_8_11_1_5961 4 120 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 139
  (Polychromatic418967fa.accept_11_3_10_7_1_129 3 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 120 139 (accept_3_3 2 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  120 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 120 139)))))))))))))))))))) (allB_succ' 21 119 139 (Eq.refl Bool.true) (allA_of_3_1 21 119 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 118 139 (Eq.refl Bool.true) (allA_succ_of_accept 21 118 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 118 139 (accept_3_3 20 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 118 139 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 118 139 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 118 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 118 139 (accept_3_3 17 118 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 118 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 118 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 118 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 118 139 (accept_3_3 14 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 118 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 118 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 118 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 139 (accept_3_3 11 118 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 139 (Polychromatic418967fa.accept_13_10_1_9_1_3380 10 118 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 118 139 (accept_3_3 8 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  118 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 118 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 118 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 139 (accept_3_3 5 118 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 139 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 118 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 118 139 (accept_3_3 2 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  118 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 118 139)))))))))))))))))))))) (allB_succ' 23 117 139 (Eq.refl Bool.true) (allA_succ_of_accept 22
  117 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 139 (Polychromatic418967fa.accept_18_3_9_13_1_1235 21 117 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 139 (accept_3_3 20 117 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 139 (Polychromatic418967fa.accept_23_19_2_1_1_7193 19 117
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 139 (accept_3_3 17 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 117 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 139 (accept_3_3 14 117 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 139 (Polychromatic418967fa.accept_25_13_17_14_1_7200 13 117 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 139
  (Polychromatic418967fa.accept_10_2_7_9_1_783 12 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 139 (accept_3_3 11 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 117 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 139 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 117 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 139 (accept_3_3 8 117 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 139 (Polychromatic418967fa.accept_15_7_12_4_1_1236 7 117
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 139 (accept_3_3 5 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 139 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 117 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 139 (accept_3_3 2 117 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 117 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117 139))))))))))))))))))))))) (allB_succ' 24 116 139
  (Eq.refl Bool.true) (allA_of_3_1 24 116 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 115 139 (Eq.refl
  Bool.true) (allA_succ_of_accept 24 115 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 115 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 139 (accept_3_3 23 115 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 139 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 115 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 139
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 139 (accept_3_3 20 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 115 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 139 (accept_3_3 17 115 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 115 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 139 (accept_3_3 14 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 139 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 115 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 139 (accept_3_3 11 115 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 115 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 139
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 139 (accept_3_3 8 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 139 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 115 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 139 (accept_3_3 5 115 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 115 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 139
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 139 (accept_3_3 2 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 139))))))))))))))))))))))))) (allB_succ' 26 114 139 (Eq.refl Bool.true) (allA_succ_of_accept
  25 114 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 114 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 114 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 114 139 (accept_3_3 23 114 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 114 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 114 139 (accept_3_3 20 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 114 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 114 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 114 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 139 (accept_3_3 17 114 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 114 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 139
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 114 139 (accept_3_3 14 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 114 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 114 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 114 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 139 (accept_3_3 11 114 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 114 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 114 139 (accept_3_3 8 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  114 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 114 139 (Polychromatic418967fa.accept_13_6_10_9_1_4329 6 114 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 139 (accept_3_3 5 114 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 114 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 139
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 114 139 (accept_3_3 2 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  114 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 114 139)))))))))))))))))))))))))) (allB_succ' 27 113 139 (Eq.refl Bool.true) (allA_of_3_1 27 113
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 112 139 (Eq.refl Bool.true) (allA_succ_of_accept 27 112
  139 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 139 (accept_3_3 26 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 139 (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 139 (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 112 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 139 (accept_3_3 23 112 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 112
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 139 (accept_3_3 20 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 139 (Polychromatic418967fa.accept_21_19_7_13_1_7189 19 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 139 (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 112 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 139 (accept_3_3 17 112 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 139 (Polychromatic418967fa.accept_13_3_8_9_1_1134 16 112
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 139 (accept_3_3 14 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 139 (Polychromatic418967fa.accept_17_13_10_3_1_7136 13 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 112 139 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 112 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 139 (accept_3_3 11 112 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 112
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 139 (accept_3_3 8 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 139 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 139 (Polychromatic418967fa.accept_21_6_7_13_1_7199 6 112 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 139 (accept_3_3 5 112 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 139 (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 112 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 139 (accept_3_3 2 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 139 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112 139)))))))))))))))))))))))))))) (allB_succ' 29 111 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 28 111 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 139 (Polychromatic418967fa.accept_17_10_9_3_1_7144 27 111
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 139 (accept_3_3 26 111
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 139
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 111 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 139 (accept_3_3 23 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 111 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 111 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 139 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 139 (accept_3_3 20
  111 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 139
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 111 139 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 139 (accept_3_3 17 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 111 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 139 (Polychromatic418967fa.accept_9_6_3_4_1_477
  15 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 139 (accept_3_3 14
  111 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 139
  (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 111 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 139 (accept_3_3 11 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 111 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 111 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 139 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 139 (accept_3_3 8 111
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 139
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 111 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 139 (accept_3_3 5 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 111 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 139 (Polychromatic418967fa.accept_13_3_7_9_1_1153
  3 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 139 (accept_3_3 2
  111 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 139
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111 139))))))))))))))))))))))))))))) (allB_succ' 30 110 139 (Eq.refl Bool.true) (allA_of_3_1 30 110 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 109 139 (Eq.refl Bool.true) (allA_succ_of_accept 30 109 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 139 (accept_3_3 29 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 139 (Polychromatic418967fa.accept_13_2_5_9_1_610 28 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 139 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 109 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 139 (accept_3_3 26 109 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 109 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 139
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 139 (accept_3_3 23 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 109 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 139 (accept_3_3 20 109 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 109 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 139 (accept_3_3 17 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 109 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 139 (accept_3_3 14 109 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 139 (Polychromatic418967fa.accept_20_13_9_19_1_5694 13 109 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 139
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 139 (accept_3_3 11 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 109 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 139 (accept_3_3 8 109 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 109 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 139 (accept_3_3 5 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 139 (Polychromatic418967fa.accept_13_4_5_9_1_1829 4 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 109 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 139 (accept_3_3 2 109 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 139 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 109 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109 139))))))))))))))))))))))))))))))) (allB_succ' 32
  108 139 (Eq.refl Bool.true) (allA_succ_of_accept 31 108 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 108 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 139
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 108 139 (accept_3_3 29 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 108 139 (Polychromatic418967fa.accept_19_9_13_6_1_7198 28 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 108 139 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 108 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 139 (accept_3_3 26 108 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 108 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 139
  (Polychromatic418967fa.accept_10_4_8_9_1_784 24 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 108 139 (accept_3_3 23 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 108 139 (Polychromatic418967fa.accept_15_7_3_4_1_574 22 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 108 139 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 108 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 139 (accept_3_3 20 108 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 139 (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 108
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 139
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 108 139 (accept_3_3 17 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 108 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 108 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 108 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 139 (accept_3_3 14 108 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 139 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 108 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 139
  (Polychromatic418967fa.accept_19_12_13_6_1_7130 12 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 108 139 (accept_3_3 11 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 139 (Polychromatic418967fa.accept_16_10_12_11_1_346 10 108 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 9
  108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 139 (accept_3_3 8 108
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 139
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 108 139 (Polychromatic418967fa.accept_13_6_4_9_1_4326 6 108 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 139 (accept_3_3 5 108 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 108 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 108 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 139 (Polychromatic418967fa.accept_14_3_10_13_1_339
  3 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 139 (accept_3_3 2
  108 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 139
  (Polychromatic418967fa.accept_10_1_8_9_1_787 1 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 139)))))))))))))))))))))))))))))))) (allB_succ' 33 107 139 (Eq.refl Bool.true) (allA_of_3_1 33 107 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 106 139 (Eq.refl Bool.true) (allA_succ_of_accept 33 106 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 106 139 (accept_3_3 32 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 106 139 (Polychromatic418967fa.accept_13_5_2_9_1_1195 31 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 106 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 106 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 106 139 (accept_3_3 29 106 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 106 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 106 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 106 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 106 139 (accept_3_3 26 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 106 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 106 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 106 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 106 139 (accept_3_3 23 106 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 106 139 (Polychromatic418967fa.accept_25_22_6_14_1_7197 22 106 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 106 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 106 139 (accept_3_3 20 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 106 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 106 139 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 106 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 106 139 (accept_3_3 17 106 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 106 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 106 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 106 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 106 139 (accept_3_3 14 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 106 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 106 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 106 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 106 139 (accept_3_3 11 106 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 106 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 106 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 106 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 106 139 (accept_3_3 8 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  106 139 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 106 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 106 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 106 139 (accept_3_3 5 106 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 106 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 106 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 106 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 106 139 (accept_3_3 2 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  106 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 106 139)))))))))))))))))))))))))))))))))) (allB_succ' 35 105 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 34 105 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 139 (Polychromatic418967fa.accept_19_14_10_6_1_4372 33 105
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 139 (accept_3_3 32 105
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 139
  (Polychromatic418967fa.accept_10_1_5_9_1_157 31 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 105 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 139 (accept_3_3 29 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 105 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 139 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 139 (accept_3_3 26
  105 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 139
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 105 139 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 139 (accept_3_3 23 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 105 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 139 (Polychromatic418967fa.accept_9_3_6_4_1_210
  21 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 139 (accept_3_3 20
  105 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 139
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 139 (accept_3_3 17 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 105 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 139 (Polychromatic418967fa.accept_12_3_9_7_1_472
  15 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 139 (accept_3_3 14
  105 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 139
  (Polychromatic418967fa.accept_19_13_10_6_1_7147 13 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 105 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 105 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 139 (accept_3_3 11 105 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 139
  (Polychromatic418967fa.accept_19_9_10_6_1_4394 9 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 139 (accept_3_3 8 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  105 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 139 (accept_3_3 5 105 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 139 (accept_3_3 2 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105 139))))))))))))))))))))))))))))))))))) (allB_succ' 36 104 139 (Eq.refl Bool.true)
  (allA_of_3_1 36 104 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 103 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 103 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 103 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 139 (accept_3_3 35 103 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 103 139 (Polychromatic418967fa.accept_10_4_3_9_1_1262 34 103 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 139
  (Polychromatic418967fa.accept_19_14_8_6_1_981 33 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 139 (accept_3_3 32 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 139 (Polychromatic418967fa.accept_16_15_7_11_1_3760 31 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 139 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 103 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 139 (accept_3_3 29 103 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 103 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 139
  (Polychromatic418967fa.accept_21_6_19_13_1_7196 27 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 103 139 (accept_3_3 26 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 103 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 103 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 139 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 103
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 139 (accept_3_3 23 103
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 139
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 103 139 (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 103 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 139 (accept_3_3 20 103 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 103 139 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 103 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 139
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 139 (accept_3_3 17 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 139 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 103 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 139 (accept_3_3 14 103 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 139 (Polychromatic418967fa.accept_19_13_8_6_1_7195 13 103 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 139
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 139 (accept_3_3 11 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 139 (Polychromatic418967fa.accept_13_10_12_9_1_1837 10 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 139 (Polychromatic418967fa.accept_15_9_13_4_1_1209 9 103 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 139 (accept_3_3 8 103 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 139 (Polychromatic418967fa.accept_19_7_8_6_1_3123 7 103 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 139
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 139 (accept_3_3 5 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 139 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 103 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 139 (accept_3_3 2 103 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 103 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 139))))))))))))))))))))))))))))))))))))) (allB_succ'
  38 102 139 (Eq.refl Bool.true) (allA_succ_of_accept 37 102 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 139
  (Polychromatic418967fa.accept_16_4_6_11_1_3753 36 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 102 139 (accept_3_3 35 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 102 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 102 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 139 (accept_3_3 32 102 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 102 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 139
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 102 139 (accept_3_3 29 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 102 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 102 139 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 102 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 139 (accept_3_3 26 102 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 139
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 139 (accept_3_3 23 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 139 (Polychromatic418967fa.accept_15_7_12_4_1_1236 22 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 139 (accept_3_3 20 102 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 102 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 139
  (Polychromatic418967fa.accept_16_2_6_11_1_1722 18 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 102 139 (accept_3_3 17 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 102 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 102 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 102 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 139 (accept_3_3 14 102 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 139
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 102 139 (accept_3_3 11 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 102 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 102 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 139 (accept_3_3 8 102 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 102 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 139 (accept_3_3 5 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 139 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 102 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 139 (accept_3_3 2 102 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 139))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 101 139 (Eq.refl Bool.true) (allA_of_3_1 39 101 139 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 100 139 (Eq.refl Bool.true) (allA_succ_of_accept 39 100 139 (Polychromatic418967fa.accept_6_3_4_1_1_8
  39 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 100 139 (accept_3_3 38
  100 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 100 139
  (Polychromatic418967fa.accept_15_7_10_4_1_151 37 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 100 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 100 139 (accept_3_3 35 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 100 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 100 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 33
  100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 139 (accept_3_3 32
  100 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 100 139
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 100 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 100 139 (accept_3_3 29 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 100 139 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 100 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 139 (accept_3_3 26 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 100 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 100 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 100 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 139 (accept_3_3 23 100 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 100 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 139 (accept_3_3 20 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 139 (Polychromatic418967fa.accept_18_1_10_13_1_500 19 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 100 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 139 (accept_3_3 17 100 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 100 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 100 139 (accept_3_3 14 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 139 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 100 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 139 (accept_3_3 11 100 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 100 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 139 (accept_3_3 8 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 100 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 139 (accept_3_3 5 100 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 100 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 139 (accept_3_3 2 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100 139)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 99 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 99 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 139 (Polychromatic418967fa.accept_16_7_3_11_1_3682 39 99
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 139 (accept_3_3 38 99 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 37
  99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 139
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 99 139 (accept_3_3 35 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  99 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 99 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 139 (accept_3_3 32 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 139 (Polychromatic418967fa.accept_16_15_3_11_1_5997 31 99 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 139
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 99 139 (accept_3_3 29 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  99 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 99 139 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 139 (accept_3_3 26 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 139 (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 99 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 139
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 99 139 (accept_3_3 23 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  99 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 99 139 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 139 (accept_3_3 20 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 99 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 139
  (Polychromatic418967fa.accept_21_18_15_13_1_4130 18 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 139 (accept_3_3 17 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 139 (Polychromatic418967fa.accept_16_15_3_11_1_5997 15 99
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 139 (accept_3_3 14 99 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 139 (Polychromatic418967fa.accept_15_13_9_4_1_3892
  13 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 139
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 99 139 (accept_3_3 11 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  99 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 99 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 139 (accept_3_3 8 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 139 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 99 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 139
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 6 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 139 (accept_3_3 5 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 99 139 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3 99 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 139 (accept_3_3 2 99 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 99 139 (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 139))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 98
  139 (Eq.refl Bool.true) (allA_of_3_1 42 98 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 97 139 (Eq.refl
  Bool.true) (allA_succ_of_accept 42 97 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 139 (accept_3_3 41 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 139 (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 97 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 139
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 139 (accept_3_3 38 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 139 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 97 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 139 (accept_3_3 35 97 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 139 (accept_3_3 32 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 139 (Polychromatic418967fa.accept_16_15_1_11_1_3747 31 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 139 (accept_3_3 29 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 97 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 139
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 139 (accept_3_3 26 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 139 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 139 (accept_3_3 23 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 139
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 139 (accept_3_3 20 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 139 (accept_3_3 17 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 139 (Polychromatic418967fa.accept_11_5_9_7_1_411 16 97 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 139 (accept_3_3 14 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 139 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 139 (accept_3_3 11 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 139
  (Polychromatic418967fa.accept_23_9_5_1_1_7194 9 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 139 (accept_3_3 8 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  139 (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 139 (accept_3_3 5 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 139 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 97 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 139
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 139 (accept_3_3 2 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  139 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 139))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 96 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 96 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 139 (Polychromatic418967fa.accept_13_3_5_9_1_5285 42 96 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 96 139 (accept_3_3 41 96 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 139 (Polychromatic418967fa.accept_13_1_5_9_1_226
  40 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 96 139
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 96 139 (accept_3_3 38 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  96 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 96 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 96 139 (accept_3_3 35 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 96 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 96 139
  (Polychromatic418967fa.accept_10_3_6_9_1_779 33 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 96 139 (accept_3_3 32 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  96 139 (Polychromatic418967fa.accept_17_14_11_3_1_4653 31 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 96 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 139 (accept_3_3 29 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 96 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 96 139
  (Polychromatic418967fa.accept_13_1_5_9_1_226 27 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 96 139 (accept_3_3 26 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  96 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 96 139 (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 139 (accept_3_3 23 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 96 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 96 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 96 139 (accept_3_3 20 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  96 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 96 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 139 (accept_3_3 17 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 96 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 96 139
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 96 139 (accept_3_3 14 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  96 139 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 96 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 139 (accept_3_3 11 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 96 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 139
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 96 139 (accept_3_3 8 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96
  139 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 96 139 (Polychromatic418967fa.accept_14_6_12_13_1_3180 6 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 139 (accept_3_3 5 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 96 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 139 (accept_3_3 2 96 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 96
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  139)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 95 139 (Eq.refl Bool.true) (allA_of_3_1 45 95 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 94 139 (Eq.refl Bool.true) (allA_succ_of_accept 45 94 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 139 (accept_3_3 44 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 139 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 139 (Polychromatic418967fa.accept_23_19_2_1_1_7193 42 94 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 139 (accept_3_3 41 94 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 94 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 139 (accept_3_3 38 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 139 (Polychromatic418967fa.accept_19_17_18_6_1_7192 36 94 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 139 (accept_3_3 35 94 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 139 (Polychromatic418967fa.accept_11_1_6_7_1_116 34 94 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 139 (accept_3_3 32 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 139 (Polychromatic418967fa.accept_13_5_3_9_1_1189 31 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 139 (accept_3_3 29 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 139 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 94 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 139 (accept_3_3 26 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 139 (Polychromatic418967fa.accept_19_5_18_6_1_7191 24 94 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 139 (accept_3_3 23 94 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 139 (Polychromatic418967fa.accept_19_3_18_6_1_3112 22 94
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 139 (accept_3_3 20 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 139 (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 139 (accept_3_3 17 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 94 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 139 (accept_3_3 14 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 139 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 139 (accept_3_3 11 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 139 (Polychromatic418967fa.accept_17_10_9_3_1_7144 10 94 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 139 (accept_3_3 8 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  139 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 94 139 (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 139 (accept_3_3 5 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 94 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 94 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 94 139 (accept_3_3 2 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94
  139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 139)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 93 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 93 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 93 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 139 (accept_3_3 44 93 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 43
  93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 93 139 (accept_3_3 41 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  93 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 93 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 139 (accept_3_3 38 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 93 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 139
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 93 139 (accept_3_3 35 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  93 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 93 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 139 (accept_3_3 32 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 93 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 139 (accept_3_3 29 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  93 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 139 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 139 (accept_3_3 26 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 93 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 139
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 139 (accept_3_3 23 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  93 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 139 (Polychromatic418967fa.accept_25_21_18_14_1_7190 21 93 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 139 (accept_3_3 20 93 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 93 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 139 (accept_3_3 17 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  93 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 139 (accept_3_3 14 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 139 (Polychromatic418967fa.accept_17_13_8_3_1_7177 13 93 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 139
  (Polychromatic418967fa.accept_17_12_8_3_1_4646 12 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 93 139 (accept_3_3 11 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  93 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 93 139 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 139 (accept_3_3 8 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 93 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 139 (accept_3_3 5 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 139 (accept_3_3 2 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 139))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  48 92 139 (Eq.refl Bool.true) (allA_of_3_1 48 92 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 91 139
  (Eq.refl Bool.true) (allA_succ_of_accept 48 91 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 91 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 139 (accept_3_3 47 91 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 139 (Polychromatic418967fa.accept_18_10_1_13_1_2192 46 91
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 139
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 139 (accept_3_3 44 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 91 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 139 (accept_3_3 41 91 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 139 (Polychromatic418967fa.accept_19_2_15_6_1_4408 40 91 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 139
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 139 (accept_3_3 38 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 139 (Polychromatic418967fa.accept_11_4_3_7_1_828 37 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 139 (Polychromatic418967fa.accept_14_8_7_13_1_4113 36 91 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 139 (accept_3_3 35 91 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 91 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 139
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 139 (accept_3_3 32 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 139 (Polychromatic418967fa.accept_17_14_6_3_1_2362 31 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 91 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 139 (accept_3_3 29 91 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 139 (Polychromatic418967fa.accept_10_8_1_9_1_413 28 91 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 139
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 27 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 139 (accept_3_3 26 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 91 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 139 (accept_3_3 23 91 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 139 (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 91 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 139
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 139 (accept_3_3 20 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 139 (Polychromatic418967fa.accept_21_19_7_13_1_7189 19 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 139 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 91 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 139 (accept_3_3 17 91 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 139
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 139 (accept_3_3 14 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 139 (Polychromatic418967fa.accept_19_13_15_6_1_7131 13 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 139 (accept_3_3 11 91 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 139 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 91 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 139
  (Polychromatic418967fa.accept_17_9_6_3_1_2398 9 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 139 (accept_3_3 8 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  139 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 91 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 139 (accept_3_3 5 91 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 139 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 91 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 139 (accept_3_3 2 91 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 139 (Polychromatic418967fa.accept_14_1_7_13_1_333 1
  91 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  139))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 90 139 (Eq.refl Bool.true) (allA_succ_of_accept 49
  90 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 90 139 (Polychromatic418967fa.accept_19_10_14_6_1_5819 48 90 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 139 (accept_3_3 47 90 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 139 (Polychromatic418967fa.accept_19_8_14_6_1_5802 46 90
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 90 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 90 139 (accept_3_3 44 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  90 139 (Polychromatic418967fa.accept_19_5_14_6_1_4413 43 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 90 139 (Polychromatic418967fa.accept_11_9_2_7_1_1298 42 90 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 139 (accept_3_3 41 90 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 139 (Polychromatic418967fa.accept_14_12_6_13_1_3173 40 90 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 139
  (Polychromatic418967fa.accept_19_1_14_6_1_1983 39 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 90 139 (accept_3_3 38 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  90 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 90 139 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 90 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 139 (accept_3_3 35 90 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 139 (Polychromatic418967fa.accept_13_8_12_9_1_1168 34 90
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 90 139 (accept_3_3 32 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  90 139 (Polychromatic418967fa.accept_11_9_2_7_1_1298 31 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 90 139 (Polychromatic418967fa.accept_19_11_14_6_1_4378 30 90 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 139 (accept_3_3 29 90 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 139 (Polychromatic418967fa.accept_16_12_10_11_1_2667 28 90
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 139
  (Polychromatic418967fa.accept_19_8_14_6_1_5802 27 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 90 139 (accept_3_3 26 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  90 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 90 139 (Polychromatic418967fa.accept_19_5_14_6_1_4413 24 90 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 139 (accept_3_3 23 90 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 139 (Polychromatic418967fa.accept_23_22_21_1_1_7188 22 90
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 90 139 (accept_3_3 20 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  90 139 (Polychromatic418967fa.accept_14_5_6_13_1_3145 19 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 90 139 (Polychromatic418967fa.accept_21_18_6_13_1_7148 18 90 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 139 (accept_3_3 17 90 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 139 (Polychromatic418967fa.accept_13_3_12_9_1_1193 16 90
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 139
  (Polychromatic418967fa.accept_16_15_10_11_1_1727 15 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 139 (accept_3_3 14 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 139 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 90
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 139 (accept_3_3 11 90 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 139
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 10 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 90 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 139 (accept_3_3 8 90 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 90 139 (Polychromatic418967fa.accept_14_7_6_13_1_4111 7 90 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 139 (Polychromatic418967fa.accept_17_6_5_3_1_7134 6
  90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 139 (accept_3_3 5 90 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 139 (Polychromatic418967fa.accept_21_4_6_13_1_7137
  4 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 139
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 139 (accept_3_3 2 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90
  139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 139)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 89 139 (Eq.refl Bool.true)
  (allA_of_3_1 51 89 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 88 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 88 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 139 (accept_3_3 50 88 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 88 139 (Polychromatic418967fa.accept_20_9_8_19_1_802 49 88 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 48
  88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 139 (accept_3_3 47 88
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 139 (Polychromatic418967fa.accept_9_1_7_4_1_52
  46 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 139 (accept_3_3 44 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 139 (Polychromatic418967fa.accept_21_1_4_13_1_7128 43 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 88 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 139 (accept_3_3 41 88 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 88 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 139 (accept_3_3 38 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 139 (Polychromatic418967fa.accept_15_6_13_4_1_2040 36 88 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 139 (accept_3_3 35 88 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 139 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 88 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 139 (accept_3_3 32 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 88 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 139 (accept_3_3 29 88 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 88 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 139 (accept_3_3 26 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 139 (Polychromatic418967fa.accept_13_12_10_9_1_1166 25 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 88 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 139 (accept_3_3 23 88 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 88 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 139 (accept_3_3 20 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 139 (Polychromatic418967fa.accept_19_18_12_6_1_7187 18 88 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 139 (accept_3_3 17 88 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 88 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 139 (accept_3_3 14 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 139 (Polychromatic418967fa.accept_16_13_8_11_1_4785 13 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 88 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 139 (accept_3_3 11 88 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 88 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 139 (accept_3_3 8 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  139 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 88 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 88 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 88 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 139 (accept_3_3 5 88 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 88 139 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 88 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 139 (accept_3_3 2 88 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 88
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  139)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 87 139 (Eq.refl Bool.true) (allA_succ_of_accept
  52 87 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 87 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 139 (accept_3_3 50 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 139 (Polychromatic418967fa.accept_27_22_6_4_1_7186 49 87 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 87 139 (accept_3_3 47 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  87 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 87 139 (Polychromatic418967fa.accept_12_9_3_7_1_924 45 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 139 (accept_3_3 44 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 87 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 139
  (Polychromatic418967fa.accept_10_2_7_9_1_783 42 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 87 139 (accept_3_3 41 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  87 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 87 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 139 (accept_3_3 38 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 87 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 139
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 87 139 (accept_3_3 35 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  87 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 87 139 (Polychromatic418967fa.accept_12_9_3_7_1_924 33 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 139 (accept_3_3 32 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 139 (Polychromatic418967fa.accept_15_1_12_4_1_2022 31 87 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 139
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 87 139 (accept_3_3 29 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  87 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 87 139 (Polychromatic418967fa.accept_21_6_3_13_1_2742 27 87 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 139 (accept_3_3 26 87 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 87 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 139
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 24 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 87 139 (accept_3_3 23 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  87 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 87 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 139 (accept_3_3 20 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 87 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 139
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 87 139 (accept_3_3 17 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  87 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 87 139 (Polychromatic418967fa.accept_16_15_7_11_1_3760 15 87 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 139 (accept_3_3 14 87 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 139 (Polychromatic418967fa.accept_19_13_11_6_1_3128 13 87
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 139
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 87 139 (accept_3_3 11 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  87 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 87 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 139 (accept_3_3 8 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 87 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 139
  (Polychromatic418967fa.accept_20_6_7_19_1_7185 6 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 139 (accept_3_3 5 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87
  139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 87 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 87 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 139 (accept_3_3 2 87 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 87 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 87 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 139)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 54 86 139 (Eq.refl Bool.true) (allA_of_3_1 54 86 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  55 85 139 (Eq.refl Bool.true) (allA_succ_of_accept 54 85 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 139 (accept_3_3 53 85 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 139 (Polychromatic418967fa.accept_15_7_10_4_1_151
  52 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 139
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 85 139 (accept_3_3 50 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  85 139 (Polychromatic418967fa.accept_14_7_1_13_1_357 49 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 85 139 (Polychromatic418967fa.accept_11_4_8_7_1_819 48 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 139 (accept_3_3 47 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 139
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 85 139 (accept_3_3 44 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  85 139 (Polychromatic418967fa.accept_13_4_7_9_1_5260 43 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 85 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 139 (accept_3_3 41 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 85 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 139
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 39 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 85 139 (accept_3_3 38 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  85 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 85 139 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 139 (accept_3_3 35 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 139
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 139 (accept_3_3 32 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 139 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 139 (accept_3_3 29 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 139 (Polychromatic418967fa.accept_13_2_7_9_1_2616 28 85 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 139
  (Polychromatic418967fa.accept_39_27_7_22_1_7184 27 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 139 (accept_3_3 26 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 139 (Polychromatic418967fa.accept_16_9_5_11_1_3776 25 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 139 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 139 (accept_3_3 23 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 139
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 139 (accept_3_3 20 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 139 (accept_3_3 17 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 85 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 139
  (Polychromatic418967fa.accept_11_4_8_7_1_819 15 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 139 (accept_3_3 14 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 139 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 139 (accept_3_3 11 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 139
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 139 (accept_3_3 8 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  139 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 85 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 139 (accept_3_3 5 85 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 139 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 85 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 139
  (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 139 (accept_3_3 2 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85
  139 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 85 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 85 139))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 84 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 84 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 139 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 84 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 139 (accept_3_3 53 84 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 52
  84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 84 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 84 139 (accept_3_3 50 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  84 139 (Polychromatic418967fa.accept_13_10_6_9_1_1152 49 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 84 139 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 84 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 139 (accept_3_3 47 84 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 84 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 84 139
  (Polychromatic418967fa.accept_10_5_4_9_1_420 45 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 84 139 (accept_3_3 44 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  84 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 84 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 84 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 139 (accept_3_3 41 84 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 139 (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 84 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 84 139
  (Polychromatic418967fa.accept_8_7_4_3_1_156 39 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 84 139 (accept_3_3 38 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  84 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 84 139 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 84 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 139 (accept_3_3 35 84 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 84 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 84 139 (accept_3_3 32 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  84 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 84 139 (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 84 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 139 (accept_3_3 29 84 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 84 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 84 139
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 84 139 (accept_3_3 26 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  84 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 84 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 84 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 139 (accept_3_3 23 84 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 139 (Polychromatic418967fa.accept_16_6_4_11_1_1719 22 84 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 84 139
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 84 139 (accept_3_3 20 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  84 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 84 139 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 84 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 139 (accept_3_3 17 84 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 84 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 139
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 84 139 (accept_3_3 14 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  84 139 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 84 139 (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 84 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 139 (accept_3_3 11 84 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 84 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 139
  (Polychromatic418967fa.accept_16_9_4_11_1_2661 9 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 84 139 (accept_3_3 8 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84
  139 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 84 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 84 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 139 (accept_3_3 5 84 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 84 139 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 84 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84 139 (Polychromatic418967fa.accept_10_3_4_9_1_15 3
  84 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 139 (accept_3_3 2 84 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  139)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 83 139 (Eq.refl Bool.true) (allA_of_3_1 57
  83 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 82 139 (Eq.refl Bool.true) (allA_succ_of_accept 57 82
  139 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 139 (accept_3_3 56 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 139 (Polychromatic418967fa.accept_15_10_7_4_1_1222 55 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 139 (Polychromatic418967fa.accept_16_6_2_11_1_7132 54 82 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 139 (accept_3_3 53 82 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 82 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 139 (accept_3_3 50 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 139 (accept_3_3 47 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 82 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 139 (accept_3_3 44 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 139 (accept_3_3 41 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 82 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 139 (accept_3_3 38 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 139 (accept_3_3 35 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 82 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 139 (accept_3_3 32 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 139 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 139 (accept_3_3 29 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 82 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 139 (accept_3_3 26 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 139 (accept_3_3 23 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 82 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 139 (accept_3_3 20 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 139 (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 139 (accept_3_3 17 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 82 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 139 (accept_3_3 14 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 139 (accept_3_3 11 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 139 (Polychromatic418967fa.accept_15_10_7_4_1_1222 10 82 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 139 (accept_3_3 8 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  139 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 82 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 82 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 139 (accept_3_3 5 82 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 82 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 82
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 139 (accept_3_3 2 82 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 81 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 81 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 139 (Polychromatic418967fa.accept_13_5_3_9_1_1189 57 81 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 139 (accept_3_3 56 81 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 139 (Polychromatic418967fa.accept_10_5_1_9_1_791
  55 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 81 139 (accept_3_3 53 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  81 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 81 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 139 (accept_3_3 50 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 139 (Polychromatic418967fa.accept_19_11_5_6_1_7183 49 81 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 139
  (Polychromatic418967fa.accept_10_8_1_9_1_413 48 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 81 139 (accept_3_3 47 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  81 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 81 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 139 (accept_3_3 44 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 139 (Polychromatic418967fa.accept_15_13_6_4_1_1221 43 81 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 81 139 (accept_3_3 41 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  81 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 81 139 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 139 (accept_3_3 38 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 81 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 139
  (Polychromatic418967fa.accept_11_3_4_7_1_114 36 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 81 139 (accept_3_3 35 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  81 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 81 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 139 (accept_3_3 32 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 81 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 81 139 (accept_3_3 29 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  81 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 81 139 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 139 (accept_3_3 26 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 139 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 81 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 139
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 81 139 (accept_3_3 23 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  81 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 81 139 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 139 (accept_3_3 20 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 81 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 81 139 (accept_3_3 17 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  81 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 81 139 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 139 (accept_3_3 14 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 139 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 81 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 139
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 81 139 (accept_3_3 11 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  81 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 81 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 139 (accept_3_3 8 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 139 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 81 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 139 (accept_3_3 5 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81
  139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 81 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 81 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 139 (accept_3_3 2 81 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 81 139 (Polychromatic418967fa.accept_19_1_5_6_1_5811 1 81 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 60 80 139 (Eq.refl Bool.true) (allA_of_3_1 60 80 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  61 79 139 (Eq.refl Bool.true) (allA_succ_of_accept 60 79 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 79 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 139 (accept_3_3 59 79 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 139 (Polychromatic418967fa.accept_13_6_1_9_1_619
  58 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 139
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 139 (accept_3_3 56 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 139 (Polychromatic418967fa.accept_13_2_1_9_1_1174 54 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 139 (accept_3_3 53 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 79 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 139 (accept_3_3 50 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 139 (Polychromatic418967fa.accept_13_10_1_9_1_3380 49 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 139 (accept_3_3 47 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 79 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 139
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 139 (accept_3_3 44 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 139 (accept_3_3 41 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 139 (Polychromatic418967fa.accept_18_4_7_13_1_3303 40 79 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 139
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 139 (accept_3_3 38 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 139 (accept_3_3 35 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 139 (Polychromatic418967fa.accept_13_8_1_9_1_1178 34 79 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 139 (accept_3_3 32 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 139 (accept_3_3 29 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 79 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 139
  (Polychromatic418967fa.accept_17_10_11_3_1_3442 27 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 139 (accept_3_3 26 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 139 (accept_3_3 23 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 79 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 139
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 139 (accept_3_3 20 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 139 (accept_3_3 17 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 139 (Polychromatic418967fa.accept_19_16_3_6_1_1941 16 79 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 139
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 139 (accept_3_3 14 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 139 (Polychromatic418967fa.accept_23_13_10_1_1_7182 13 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 139 (accept_3_3 11 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 79 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 139
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 139 (accept_3_3 8 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  139 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 139 (accept_3_3 5 79 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 79 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 139
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 139 (accept_3_3 2 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  139 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 79 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 139))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 78 139 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 78 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 139 (Polychromatic418967fa.accept_17_9_10_3_1_3423
  60 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 139 (accept_3_3 59
  78 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 139
  (Polychromatic418967fa.accept_7_2_1_6_1_173 58 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 78 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 139 (accept_3_3 56 78 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 78 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 78 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 54
  78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 139 (accept_3_3 53 78
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 139
  (Polychromatic418967fa.accept_9_7_6_4_1_483 52 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 78 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 78 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 139 (accept_3_3 50 78 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 78 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 48
  78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 139 (accept_3_3 47 78
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 139 (Polychromatic418967fa.accept_9_1_6_4_1_49
  46 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 78 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 78 139 (accept_3_3 44 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  78 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 78 139 (Polychromatic418967fa.accept_19_4_2_6_1_7181 42 78 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 139 (accept_3_3 41 78 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 78 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 78 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 78 139 (accept_3_3 38 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  78 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 78 139 (Polychromatic418967fa.accept_24_12_6_19_1_7180 36 78 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 139 (accept_3_3 35 78 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 78 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 78 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 78 139 (accept_3_3 32 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  78 139 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 78 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 78 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 139 (accept_3_3 29 78 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 78 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 78 139
  (Polychromatic418967fa.accept_10_7_8_9_1_785 27 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 78 139 (accept_3_3 26 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  78 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 78 139 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 78 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 139 (accept_3_3 23 78 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 139 (Polychromatic418967fa.accept_15_7_3_4_1_574 22 78 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 78 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 78 139 (accept_3_3 20 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  78 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 78 139 (Polychromatic418967fa.accept_21_18_15_13_1_4130 18 78 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 139 (accept_3_3 17 78 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 78 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 78 139
  (Polychromatic418967fa.accept_19_15_2_6_1_7179 15 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 78 139 (accept_3_3 14 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  78 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 78 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 78 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 139 (accept_3_3 11 78 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 78 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 78 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 139 (accept_3_3 8 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78
  139 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 78 139 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 78 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 139 (accept_3_3 5 78 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 78 139 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 78 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  78 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 139 (accept_3_3 2 78 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 77 139 (Eq.refl Bool.true)
  (allA_of_3_1 63 77 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 76 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 76 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 139 (accept_3_3 62 76 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 76 139 (Polychromatic418967fa.accept_14_5_6_13_1_3145 61 76 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 139
  (Polychromatic418967fa.accept_13_8_11_9_1_593 60 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 139 (accept_3_3 59 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 139 (Polychromatic418967fa.accept_11_3_10_7_1_129 58 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 76 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 139 (accept_3_3 56 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 76 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 139
  (Polychromatic418967fa.accept_13_2_11_9_1_591 54 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 139 (accept_3_3 53 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 139 (Polychromatic418967fa.accept_16_4_12_11_1_2650 52 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 139 (accept_3_3 50 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 139 (Polychromatic418967fa.accept_14_7_6_13_1_4111 49 76 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 139
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 48 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 139 (accept_3_3 47 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 139 (accept_3_3 44 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 139 (Polychromatic418967fa.accept_10_3_6_9_1_779 43 76 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 139
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 42 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 139 (accept_3_3 41 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 139 (Polychromatic418967fa.accept_13_1_11_9_1_1857 40 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 139 (accept_3_3 38 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 139 (Polychromatic418967fa.accept_20_17_16_19_1_7178 37 76 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 139
  (Polychromatic418967fa.accept_11_3_10_7_1_129 36 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 139 (accept_3_3 35 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 139 (accept_3_3 32 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 76 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 139
  (Polychromatic418967fa.accept_17_13_8_3_1_7177 30 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 139 (accept_3_3 29 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 139 (Polychromatic418967fa.accept_13_2_11_9_1_591 28 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 139 (accept_3_3 26 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 139 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 76 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 139
  (Polychromatic418967fa.accept_16_8_12_11_1_3697 24 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 139 (accept_3_3 23 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 139 (accept_3_3 20 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 139 (Polychromatic418967fa.accept_14_5_6_13_1_3145 19 76 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 139
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 139 (accept_3_3 17 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 139 (Polychromatic418967fa.accept_22_16_10_7_1_5554 16 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 139 (accept_3_3 14 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 139 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 76 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 139
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 139 (accept_3_3 11 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 139 (accept_3_3 8 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 76 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 139
  (Polychromatic418967fa.accept_23_6_7_1_1_7176 6 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 139 (accept_3_3 5 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  139 (Polychromatic418967fa.accept_16_4_12_11_1_2650 4 76 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 76 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 139 (accept_3_3 2 76 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 139 (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 76 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 75 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 64 75 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 139 (Polychromatic418967fa.accept_17_12_7_3_1_1498 63 75
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 139 (accept_3_3 62 75 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 61
  75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 139
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 75 139 (accept_3_3 59 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  75 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 75 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 139 (accept_3_3 56 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 75 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 139
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 139 (accept_3_3 53 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 139 (accept_3_3 50 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 139 (Polychromatic418967fa.accept_11_5_9_7_1_411 49 75 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 139
  (Polychromatic418967fa.accept_14_6_5_13_1_367 48 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 139 (accept_3_3 47 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  75 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 139 (Polychromatic418967fa.accept_12_9_3_7_1_924 45 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 139 (accept_3_3 44 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 75 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 139 (accept_3_3 41 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 139 (accept_3_3 38 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 75 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 139
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 139 (accept_3_3 35 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 139 (accept_3_3 32 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 139 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 75 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 139
  (Polychromatic418967fa.accept_18_12_3_13_1_4494 30 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 139 (accept_3_3 29 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 139 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 139 (accept_3_3 26 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 75 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 139 (accept_3_3 23 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 139 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 139 (accept_3_3 20 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 75 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 139
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 139 (accept_3_3 17 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 139 (accept_3_3 14 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 139 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 75 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 139
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 139 (accept_3_3 11 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 139 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 139 (accept_3_3 8 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 75 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 139 (accept_3_3 5 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 139 (Polychromatic418967fa.accept_19_3_18_6_1_3112 3 75 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 139 (accept_3_3 2 75 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 75 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  139))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 74 139 (Eq.refl Bool.true)
  (allA_of_3_1 66 74 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 73 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 73 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 73 139 (accept_3_3 65 73 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 73 139 (Polychromatic418967fa.accept_10_4_3_9_1_1262 64 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 73 139 (Polychromatic418967fa.accept_13_11_8_9_1_1161
  63 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 139 (accept_3_3 62
  73 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 139
  (Polychromatic418967fa.accept_9_7_1_4_1_217 61 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 73 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 73 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 73 139 (accept_3_3 59 73 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 73 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 73 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 57
  73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 139 (accept_3_3 56 73
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 139
  (Polychromatic418967fa.accept_13_3_8_9_1_1134 55 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 73 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 139 (accept_3_3 53 73 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 73 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 51
  73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 139 (accept_3_3 50 73
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 139
  (Polychromatic418967fa.accept_19_11_16_6_1_7155 49 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 73 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 73 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 139 (accept_3_3 47 73 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 73 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 139 (Polychromatic418967fa.accept_19_7_16_6_1_4400
  45 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 139 (accept_3_3 44
  73 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 139
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 73 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 139 (accept_3_3 41 73 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 73 139 (Polychromatic418967fa.accept_13_1_8_9_1_1154 40 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 39
  73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 139 (accept_3_3 38 73
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 139 (Polychromatic418967fa.accept_7_2_3_6_1_4
  37 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 139
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 139 (accept_3_3 35 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 139 (accept_3_3 32 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 139 (Polychromatic418967fa.accept_19_12_16_6_1_7175 31 73 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 139 (accept_3_3 29 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 139 (Polychromatic418967fa.accept_18_10_1_13_1_2192 28 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 139 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 139 (accept_3_3 26 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 73 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 139
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 139 (accept_3_3 23 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 139 (accept_3_3 20 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 139 (Polychromatic418967fa.accept_17_2_5_3_1_1416 19 73 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 139 (accept_3_3 17 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 139 (accept_3_3 14 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 139 (Polychromatic418967fa.accept_24_13_1_19_1_7174 13 73 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 139
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 139 (accept_3_3 11 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 139 (accept_3_3 8 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 139 (accept_3_3 5 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  139 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 73 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 73 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 139 (accept_3_3 2 73 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 139 (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 73 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  139))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 72 139 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 72 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 72 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 72 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 139 (accept_3_3 65 72 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 64
  72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 72 139
  (Polychromatic418967fa.accept_13_11_7_9_1_612 63 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 72 139 (accept_3_3 62 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  72 139 (Polychromatic418967fa.accept_10_1_2_9_1_152 61 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 72 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 139 (accept_3_3 59 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 72 139 (Polychromatic418967fa.accept_13_6_7_9_1_1848 58 72 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 72 139
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 72 139 (accept_3_3 56 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  72 139 (Polychromatic418967fa.accept_13_3_7_9_1_1153 55 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 72 139 (Polychromatic418967fa.accept_13_2_7_9_1_2616 54 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 139 (accept_3_3 53 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 72 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 72 139
  (Polychromatic418967fa.accept_10_1_2_9_1_152 51 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 72 139 (accept_3_3 50 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  72 139 (Polychromatic418967fa.accept_19_11_15_6_1_7173 49 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 72 139 (Polychromatic418967fa.accept_19_10_15_6_1_5772 48 72 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 139 (accept_3_3 47 72 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 72 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 72 139
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 72 139 (accept_3_3 44 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  72 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 72 139 (Polychromatic418967fa.accept_13_3_7_9_1_1153 42 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 139 (accept_3_3 41 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 139 (Polychromatic418967fa.accept_19_2_15_6_1_4408 40 72 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 72 139
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 72 139 (accept_3_3 38 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  72 139 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 72 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 139 (accept_3_3 35 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 139 (Polychromatic418967fa.accept_11_1_6_7_1_116 34 72 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 72 139
  (Polychromatic418967fa.accept_17_16_4_3_1_3429 33 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 72 139 (accept_3_3 32 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  72 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 72 139 (Polychromatic418967fa.accept_13_4_7_9_1_5260 30 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 139 (accept_3_3 29 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 139 (Polychromatic418967fa.accept_13_2_7_9_1_2616 28 72 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 72 139
  (Polychromatic418967fa.accept_10_7_2_9_1_775 27 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 72 139 (accept_3_3 26 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  72 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 72 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 139 (accept_3_3 23 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 72 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 72 139
  (Polychromatic418967fa.accept_10_1_2_9_1_152 21 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 72 139 (accept_3_3 20 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  72 139 (Polychromatic418967fa.accept_13_6_7_9_1_1848 19 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 72 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 139 (accept_3_3 17 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 139 (Polychromatic418967fa.accept_13_3_7_9_1_1153 16 72 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 72 139
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 72 139 (accept_3_3 14 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  72 139 (Polychromatic418967fa.accept_16_13_8_11_1_4785 13 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 72 139 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 139 (accept_3_3 11 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 72 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 72 139
  (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 72 139 (accept_3_3 8 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72
  139 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 72 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 72 139 (Polychromatic418967fa.accept_13_6_7_9_1_1848 6 72 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 139 (accept_3_3 5 72 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 72 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 72 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 139 (accept_3_3 2 72 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 71 139 (Eq.refl Bool.true)
  (allA_of_3_1 69 71 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 139 (allA_succ_of_accept 69 70 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 139 (accept_3_3 68 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 139 (Polychromatic418967fa.accept_13_2_5_9_1_610 67 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 139 (accept_3_3 65 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 70 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 139 (accept_3_3 62 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 139 (accept_3_3 59 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 139 (Polychromatic418967fa.accept_11_3_4_7_1_114 58 70 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 139 (accept_3_3 56 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 139 (Polychromatic418967fa.accept_13_2_5_9_1_610 54 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 139 (accept_3_3 53 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 139 (Polychromatic418967fa.accept_11_8_4_7_1_1303 52 70 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 139 (accept_3_3 50 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 139 (accept_3_3 47 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 70 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 139 (accept_3_3 44 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 139 (Polychromatic418967fa.accept_13_4_5_9_1_1829 43 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 139 (accept_3_3 41 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 70 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 139 (accept_3_3 38 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 139 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 139 (accept_3_3 35 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 139 (Polychromatic418967fa.accept_16_2_6_11_1_1722 34 70 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 139 (accept_3_3 32 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 139 (Polychromatic418967fa.accept_17_14_2_3_1_7172 31 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 139 (accept_3_3 29 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 70 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 139 (accept_3_3 26 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 139 (accept_3_3 23 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 139 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 70 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 139 (accept_3_3 20 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 139 (Polychromatic418967fa.accept_16_2_6_11_1_1722 18 70 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 139 (accept_3_3 17 70 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 70 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 139 (accept_3_3 14 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 139 (accept_3_3 11 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 70 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 139 (accept_3_3 8 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  139 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 70 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 139 (accept_3_3 5 70 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 70 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 139 (accept_3_3 2 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 139
  (allA_succ_of_accept 68 69 139 (accept_3_3 68 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 139 (Polychromatic418967fa.accept_19_10_12_6_1_7171 67 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 139 (accept_3_3 65 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 139
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 139 (accept_3_3 62 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 139 (Polychromatic418967fa.accept_13_8_4_9_1_1145 60 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 139 (accept_3_3 59 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 139 (accept_3_3 56 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 139 (accept_3_3 53 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 139
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 139 (accept_3_3 50 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 139 (Polychromatic418967fa.accept_17_15_1_3_1_1488 49 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 139 (accept_3_3 47 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 139
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 139 (accept_3_3 44 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 139 (accept_3_3 41 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 139 (accept_3_3 38 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 139 (Polychromatic418967fa.accept_15_6_9_4_1_1227 36 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 139 (accept_3_3 35 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 139
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 33 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 139 (accept_3_3 32 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 139 (Polychromatic418967fa.accept_13_5_4_9_1_601 31 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 139 (accept_3_3 29 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 139
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 139 (accept_3_3 26 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 139 (Polychromatic418967fa.accept_16_8_5_11_1_4776 24 69 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 139 (accept_3_3 23 69 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 139 (accept_3_3 20 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 139 (accept_3_3 17 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 139
  (Polychromatic418967fa.accept_11_4_3_7_1_828 15 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 139 (accept_3_3 14 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 139 (Polychromatic418967fa.accept_15_13_9_4_1_3892 13 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 139 (accept_3_3 11 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 139
  (Polychromatic418967fa.accept_16_9_5_11_1_3776 9 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 139 (accept_3_3 8 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  139 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 139 (accept_3_3 5 69 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  69 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 139 (accept_3_3 2 69 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 69
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  139))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 139 (allA_of_3_1 68 68 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 139 (allA_succ_of_accept 66 67 139
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 139 (accept_3_3 65 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 139 (Polychromatic418967fa.accept_17_13_16_3_1_1431 64 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 139 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 139 (accept_3_3 62 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 67 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 139
  (Polychromatic418967fa.accept_21_18_4_13_1_5602 60 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 139 (accept_3_3 59 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 139 (Polychromatic418967fa.accept_13_5_2_9_1_1195 57 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 139 (accept_3_3 56 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 139 (Polychromatic418967fa.accept_13_3_2_9_1_1187 55 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 139
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 139 (accept_3_3 53 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 139 (accept_3_3 50 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 139 (Polychromatic418967fa.accept_21_7_4_13_1_4125 49 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 139
  (Polychromatic418967fa.accept_10_8_7_9_1_425 48 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 139 (accept_3_3 47 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 139 (Polychromatic418967fa.accept_13_7_2_9_1_1826 46 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 139 (accept_3_3 44 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 139 (Polychromatic418967fa.accept_21_1_4_13_1_7128 43 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 139
  (Polychromatic418967fa.accept_10_2_7_9_1_783 42 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 139 (accept_3_3 41 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 139 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 139 (accept_3_3 38 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 139
  (Polychromatic418967fa.accept_27_9_13_4_1_7170 36 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 139 (accept_3_3 35 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 139 (Polychromatic418967fa.accept_19_15_10_6_1_7169 34 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 139 (accept_3_3 32 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 139
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 139 (accept_3_3 29 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 139 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 139 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 139 (accept_3_3 26 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 139 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 139
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 139 (accept_3_3 23 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 139 (Polychromatic418967fa.accept_10_2_7_9_1_783 22 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 139 (Polychromatic418967fa.accept_17_4_16_3_1_4620 21 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 139 (accept_3_3 20 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 67 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 139
  (Polychromatic418967fa.accept_10_8_7_9_1_425 18 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 139 (accept_3_3 17 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 139 (Polychromatic418967fa.accept_16_15_3_11_1_5997 15 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 139 (accept_3_3 14 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 139 (Polychromatic418967fa.accept_17_13_16_3_1_1431 13 67
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 139
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 139 (accept_3_3 11 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 139 (accept_3_3 8 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 139 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 139
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 139 (accept_3_3 5 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  139 (Polychromatic418967fa.accept_17_4_16_3_1_4620 4 67 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 139 (accept_3_3 2 67 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 139 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 67 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  139))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 139 (allA_succ_of_accept 65 66
  139 (accept_3_3 65 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 139
  (Polychromatic418967fa.accept_9_1_3_4_1_47 64 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 139 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 66 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 139 (accept_3_3 62 66 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 60
  66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 139 (accept_3_3 59 66
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 139 (Polychromatic418967fa.accept_7_2_3_6_1_4
  58 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 66 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 66 139 (accept_3_3 56 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  66 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 66 139 (Polychromatic418967fa.accept_13_2_1_9_1_1174 54 66 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 139 (accept_3_3 53 66 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 66 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 66 139
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 66 139 (accept_3_3 50 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  66 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 66 139 (Polychromatic418967fa.accept_17_14_15_3_1_4618 48 66 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 139 (accept_3_3 47 66 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 66 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 66 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 66 139 (accept_3_3 44 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  66 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 66 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 66 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 139 (accept_3_3 41 66 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 139 (Polychromatic418967fa.accept_15_10_6_4_1_1256 40 66 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 139
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 66 139 (accept_3_3 38 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  66 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 66 139 (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 66 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 139 (accept_3_3 35 66 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 66 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 66 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 66 139 (accept_3_3 32 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  66 139 (Polychromatic418967fa.accept_13_5_1_9_1_618 31 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 66 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 66 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 139 (accept_3_3 29 66 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 66 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 139
  (Polychromatic418967fa.accept_20_7_6_19_1_2949 27 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 66 139 (accept_3_3 26 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  66 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 66 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 66 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 139 (accept_3_3 23 66 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 139 (Polychromatic418967fa.accept_16_6_2_11_1_7132 22 66 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 66 139 (accept_3_3 20 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  66 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 66 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 66 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 139 (accept_3_3 17 66 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 66 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 139 (accept_3_3 14 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  66 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 139 (Polychromatic418967fa.accept_17_12_15_3_1_7168 12 66 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 139 (accept_3_3 11 66 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 66 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 139 (accept_3_3 8 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66
  139 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 66 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 66 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 139 (accept_3_3 5 66 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 66 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 66 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 139 (Polychromatic418967fa.accept_10_3_6_9_1_779 3
  66 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 139 (accept_3_3 2 66 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 139 (allA_of_3_1 65 65 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 139 (allA_succ_of_accept 63 64 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 139 (accept_3_3 62 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 139 (accept_3_3 59 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 64 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 139 (accept_3_3 56 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 139 (Polychromatic418967fa.accept_10_5_4_9_1_420 55 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 139 (accept_3_3 53 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 64 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 139 (accept_3_3 50 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 139 (Polychromatic418967fa.accept_11_5_9_7_1_411 49 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 139 (accept_3_3 47 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 139 (Polychromatic418967fa.accept_11_2_9_7_1_124 46 64 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 139 (accept_3_3 44 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 139 (accept_3_3 41 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 64 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 139 (accept_3_3 38 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 139 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 64 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 139 (accept_3_3 35 64 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 64 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 139 (accept_3_3 32 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 139 (Polychromatic418967fa.accept_21_10_1_13_1_7167 31 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 139 (accept_3_3 29 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 139 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 64 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 139 (accept_3_3 26 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 139 (accept_3_3 23 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 64 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 139 (accept_3_3 20 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 139 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 139 (accept_3_3 17 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 64 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 139 (accept_3_3 14 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 139 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 139 (accept_3_3 11 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 64 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 139 (accept_3_3 8 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  139 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 64 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 139 (accept_3_3 5 64 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 139 (Polychromatic418967fa.accept_17_4_13_3_1_7166 4 64 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 139 (accept_3_3 2 64 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 139 (Polychromatic418967fa.accept_18_1_10_13_1_500
  1 64 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 139 (allA_succ_of_accept 62 63 139
  (accept_3_3 62 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 139
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 61 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 63 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 139 (accept_3_3 59 63 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 63 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 139 (Polychromatic418967fa.accept_12_9_3_7_1_924
  57 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 139 (accept_3_3 56
  63 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 139
  (Polychromatic418967fa.accept_16_7_15_11_1_951 55 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 139 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 63 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 139 (accept_3_3 53 63 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 63 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 139
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 51 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 139 (accept_3_3 50 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 139 (Polychromatic418967fa.accept_16_1_15_11_1_356 49 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 139 (Polychromatic418967fa.accept_11_4_8_7_1_819 48 63 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 139 (accept_3_3 47 63 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 63 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 139
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 139 (accept_3_3 44 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 139 (Polychromatic418967fa.accept_14_1_7_13_1_333 43 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 139 (Polychromatic418967fa.accept_16_10_15_11_1_3785 42 63 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 139 (accept_3_3 41 63 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 139
  (Polychromatic418967fa.accept_16_7_15_11_1_951 39 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 139 (accept_3_3 38 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 139 (Polychromatic418967fa.accept_11_4_8_7_1_819 37 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 139 (accept_3_3 35 63 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 63 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 139
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 139 (accept_3_3 32 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 139 (Polychromatic418967fa.accept_15_1_3_4_1_1217 31 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 139 (Polychromatic418967fa.accept_20_10_3_19_1_2931 30 63 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 139 (accept_3_3 29 63 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 139
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 139 (accept_3_3 26 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 139 (Polychromatic418967fa.accept_17_8_12_3_1_5927 25 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 139 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 63 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 139 (accept_3_3 23 63 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 63 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 139
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 139 (accept_3_3 20 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 139 (Polychromatic418967fa.accept_16_3_15_11_1_2676 19 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 139 (Polychromatic418967fa.accept_22_18_19_7_1_7165 18 63 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 139 (accept_3_3 17 63 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 139
  (Polychromatic418967fa.accept_11_4_8_7_1_819 15 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 139 (accept_3_3 14 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 139 (Polychromatic418967fa.accept_22_13_19_7_1_2558 13 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 139 (accept_3_3 11 63 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 63 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 139
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 139 (accept_3_3 8 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  139 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 139 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 63 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 139 (accept_3_3 5 63 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 139
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 3 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 139 (accept_3_3 2 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  139 (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 63 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 139))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 139
  (allA_of_3_1 62 62 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 139 (allA_succ_of_accept 60 61 139
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 139 (accept_3_3 59 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 139 (accept_3_3 56 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 61 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 139 (accept_3_3 53 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 139 (Polychromatic418967fa.accept_10_2_1_9_1_1248 52 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 139 (accept_3_3 50 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 139 (Polychromatic418967fa.accept_21_7_19_13_1_7164 49 61 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 139
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 139 (accept_3_3 47 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 139 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 139 (accept_3_3 44 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 61 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 139 (accept_3_3 41 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 139 (Polychromatic418967fa.accept_16_8_13_11_1_4772 40 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 139 (accept_3_3 38 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 61 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 139
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 139 (accept_3_3 35 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 139 (accept_3_3 32 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 139 (Polychromatic418967fa.accept_19_12_4_6_1_7163 31 61 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 139 (accept_3_3 29 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 139 (Polychromatic418967fa.accept_15_12_1_4_1_2899 27 61 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 139 (accept_3_3 26 61 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 61 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 139 (accept_3_3 23 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 139 (accept_3_3 20 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 139 (accept_3_3 17 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 139 (Polychromatic418967fa.accept_21_16_19_13_1_7140 16 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 139 (accept_3_3 14 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 139 (Polychromatic418967fa.accept_17_13_10_3_1_7136 13 61 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 139
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 139 (accept_3_3 11 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 139 (Polychromatic418967fa.accept_17_9_10_3_1_3423 9 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 139 (accept_3_3 8 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 139 (Polychromatic418967fa.accept_17_7_10_3_1_1421 7 61 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 139 (accept_3_3 5 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  139 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 61 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 139 (accept_3_3 2 61 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 139 (allA_succ_of_accept 59 60 139 (accept_3_3 59 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 60 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 60 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 139 (accept_3_3 56 60 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 55
  60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 139
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 139 (accept_3_3 53 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 139 (accept_3_3 50 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 139 (Polychromatic418967fa.accept_16_1_12_11_1_2648 49 60 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 60 139 (accept_3_3 47 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  60 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 60 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 139 (accept_3_3 44 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 60 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 139
  (Polychromatic418967fa.accept_11_9_5_7_1_815 42 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 139 (accept_3_3 41 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  60 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 60 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 139 (accept_3_3 38 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 60 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 139
  (Polychromatic418967fa.accept_16_4_12_11_1_2650 36 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 139 (accept_3_3 35 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 139 (accept_3_3 32 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 60 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 139
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 139 (accept_3_3 29 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 139 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 139 (accept_3_3 26 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 60 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 139
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 139 (accept_3_3 23 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 139 (Polychromatic418967fa.accept_25_22_10_14_1_7162 22 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 139 (accept_3_3 20 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 60 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 139
  (Polychromatic418967fa.accept_17_1_9_3_1_7161 18 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 139 (accept_3_3 17 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 139 (accept_3_3 14 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 139 (Polychromatic418967fa.accept_22_13_16_7_1_7160 13 60 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 139
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 139 (accept_3_3 11 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 139 (accept_3_3 8 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 139
  (Polychromatic418967fa.accept_17_6_9_3_1_704 6 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 139 (accept_3_3 5 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  139 (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 60 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 60 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 139 (accept_3_3 2 60 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 60 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 139 (allA_of_3_1 59 59 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 58 139 (allA_succ_of_accept 57 58 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 58 139 (accept_3_3 56 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  58 139 (Polychromatic418967fa.accept_13_3_6_9_1_1150 55 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 58 139 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 139 (accept_3_3 53 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 58 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 139 (accept_3_3 50 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 139 (Polychromatic418967fa.accept_11_4_3_7_1_828 48 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 139 (accept_3_3 47 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 58 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 139 (accept_3_3 44 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 139 (Polychromatic418967fa.accept_13_3_6_9_1_1150 42 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 139 (accept_3_3 41 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 58 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 139 (accept_3_3 38 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 139 (accept_3_3 35 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 139 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 58 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 139 (accept_3_3 32 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 139 (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 139 (accept_3_3 29 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 58 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 139 (accept_3_3 26 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 139 (accept_3_3 23 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 58 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 139 (accept_3_3 20 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 139 (Polychromatic418967fa.accept_21_19_16_13_1_4099 19 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 139 (accept_3_3 17 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 58 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 139 (accept_3_3 14 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 139 (Polychromatic418967fa.accept_16_12_10_11_1_2667 12 58 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 139 (accept_3_3 11 58 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 58 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 139 (accept_3_3 8 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  139 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 58 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 139 (Polychromatic418967fa.accept_15_6_13_4_1_2040 6 58 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 139 (accept_3_3 5 58 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 58 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 58
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 139 (accept_3_3 2 58 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 139 (allA_succ_of_accept 56 57 139
  (accept_3_3 56 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 139
  (Polychromatic418967fa.accept_9_1_3_4_1_47 55 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 139 (accept_3_3 53 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 51
  57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 139 (accept_3_3 50 57
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 139
  (Polychromatic418967fa.accept_14_7_1_13_1_357 49 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 139 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 139 (accept_3_3 47 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 139 (Polychromatic418967fa.accept_18_9_3_13_1_5905
  45 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 139 (accept_3_3 44
  57 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 139
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 139 (accept_3_3 41 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 139 (Polychromatic418967fa.accept_12_3_9_7_1_472
  39 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 139 (accept_3_3 38
  57 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 139
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 139 (Polychromatic418967fa.accept_16_4_9_11_1_7159 36 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 139 (accept_3_3 35 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 33
  57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 139 (accept_3_3 32 57
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 139
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 31 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 139 (accept_3_3 29 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 139 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 139 (accept_3_3 26
  57 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 139
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 139 (accept_3_3 23 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 139 (Polychromatic418967fa.accept_14_7_1_13_1_357
  21 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 139 (accept_3_3 20
  57 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 139
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 139 (accept_3_3 17 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 15
  57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 139 (accept_3_3 14 57
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 139
  (Polychromatic418967fa.accept_23_13_11_1_1_7158 13 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 139 (accept_3_3 11 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 9
  57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 139 (accept_3_3 8 57 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 7
  57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 139 (accept_3_3 5 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 139 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 139 (accept_3_3 2 57 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 57 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 139 (allA_of_3_1 56 56 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 139
  (allA_succ_of_accept 54 55 139 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 139 (accept_3_3 53 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 51
  55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 139 (accept_3_3 50 55
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 139
  (Polychromatic418967fa.accept_19_11_17_6_1_7157 49 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 139 (accept_3_3 47 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 139 (Polychromatic418967fa.accept_10_6_5_9_1_1233 46 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 139 (Polychromatic418967fa.accept_13_6_3_9_1_1827
  45 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 139 (accept_3_3 44
  55 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 139
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 55 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 139 (accept_3_3 41 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 55 139 (Polychromatic418967fa.accept_22_18_11_7_1_7156 40 55 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 139
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 139 (accept_3_3 38 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 139 (Polychromatic418967fa.accept_15_7_10_4_1_151 37 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 139 (accept_3_3 35 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 55 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 139
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 139 (accept_3_3 32 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 139 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 139 (accept_3_3 29 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 55 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 139
  (Polychromatic418967fa.accept_19_8_17_6_1_5728 27 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 139 (accept_3_3 26 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 139 (accept_3_3 23 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 139 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 55 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 139
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 139 (accept_3_3 20 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 139 (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 139 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 139 (accept_3_3 17 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 55 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 139
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 139 (accept_3_3 14 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 139 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 139 (accept_3_3 11 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 139 (Polychromatic418967fa.accept_18_10_1_13_1_2192 10 55 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 139
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 139 (accept_3_3 8 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  139 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 139 (accept_3_3 5 55 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 55 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 139 (accept_3_3 2 55 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 139 (Polychromatic418967fa.accept_10_1_5_9_1_157 1
  55 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  139))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 139 (allA_succ_of_accept 53 54 139
  (accept_3_3 53 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 139
  (Polychromatic418967fa.accept_16_4_6_11_1_3753 52 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 54 139 (Polychromatic418967fa.accept_15_6_9_4_1_1227 51 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 139 (accept_3_3 50 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 54 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 139 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  48 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 139 (accept_3_3 47
  54 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 139
  (Polychromatic418967fa.accept_7_4_5_6_1_344 46 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 54 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 139 (accept_3_3 44 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 54 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 139 (Polychromatic418967fa.accept_13_3_2_9_1_1187
  42 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 54 139 (accept_3_3 41
  54 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 139
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 40 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 54 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 139 (accept_3_3 38 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 54 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 36
  54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 54 139 (accept_3_3 35 54
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 139
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 34 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 54 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 139 (accept_3_3 32 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 54 139 (Polychromatic418967fa.accept_13_5_2_9_1_1195 31 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 139
  (Polychromatic418967fa.accept_19_11_16_6_1_7155 30 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 139 (accept_3_3 29 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 139 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 139 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 139 (accept_3_3 26 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 139
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 139 (accept_3_3 23 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 139 (accept_3_3 20 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 139 (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 54 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 139
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 139 (accept_3_3 17 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 139 (Polychromatic418967fa.accept_13_3_2_9_1_1187 16 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 139 (accept_3_3 14 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 139
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 139 (accept_3_3 11 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 139 (Polychromatic418967fa.accept_15_10_9_4_1_2924 10 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 139 (accept_3_3 8 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 139 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 54 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 139
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 6 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 139 (accept_3_3 5 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  139 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 54 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 54 139 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 139 (accept_3_3 2 54 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 54 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 139))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 139 (allA_of_3_1 53 53 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 139
  (allA_succ_of_accept 51 52 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 139 (accept_3_3 50 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 139 (Polychromatic418967fa.accept_17_15_1_3_1_1488 49 52 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 139
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 139 (accept_3_3 47 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 139 (accept_3_3 44 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 139 (Polychromatic418967fa.accept_17_9_1_3_1_4626 43 52 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 139 (accept_3_3 41 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 139 (Polychromatic418967fa.accept_15_10_7_4_1_1222 40 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 139 (accept_3_3 38 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 52 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 139
  (Polychromatic418967fa.accept_17_2_1_3_1_2357 36 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 139 (accept_3_3 35 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 139 (accept_3_3 32 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 52 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 139
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 139 (accept_3_3 29 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 139 (accept_3_3 26 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 52 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 139 (accept_3_3 23 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 139 (accept_3_3 20 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 52 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 139
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 139 (accept_3_3 17 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 139 (accept_3_3 14 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 139 (Polychromatic418967fa.accept_20_13_12_19_1_7154 13 52 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 139
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 139 (accept_3_3 11 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 139 (accept_3_3 8 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 52 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 139 (accept_3_3 5 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  139 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 52 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 139 (accept_3_3 2 52 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 52 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 139))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 139 (allA_succ_of_accept 50 51 139 (accept_3_3 50 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 139 (Polychromatic418967fa.accept_13_10_12_9_1_1837 49 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 51 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 139 (accept_3_3 47 51 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 46
  51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 139
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 139 (accept_3_3 44 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 139 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 139 (accept_3_3 41 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 139
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 139 (accept_3_3 38 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 139 (accept_3_3 35 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 51 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 139
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 139 (accept_3_3 32 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 139 (accept_3_3 29 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 139
  (Polychromatic418967fa.accept_19_8_13_6_1_7153 27 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 139 (accept_3_3 26 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 139 (accept_3_3 23 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 51 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 139 (accept_3_3 20 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 139 (accept_3_3 17 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 139
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 139 (accept_3_3 14 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 139 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 139 (accept_3_3 11 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 51 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 139
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 139 (accept_3_3 8 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  139 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 51 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 139 (Polychromatic418967fa.accept_16_6_3_11_1_3751 6 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 139 (accept_3_3 5 51 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 139 (accept_3_3 2 51 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 51
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  139))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 139 (allA_of_3_1 50 50 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 139 (allA_succ_of_accept 48 49 139 (Polychromatic418967fa.accept_14_6_7_13_1_3158
  48 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 139 (accept_3_3 47
  49 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 49 139 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 139 (accept_3_3 44 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 49 139 (Polychromatic418967fa.accept_14_1_7_13_1_333 43 49 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 139 (accept_3_3 41 49
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 139
  (Polychromatic418967fa.accept_13_1_10_9_1_215 40 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 49 139 (Polychromatic418967fa.accept_19_1_11_6_1_7152 39 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 139 (accept_3_3 38 49 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 49 139 (Polychromatic418967fa.accept_19_18_11_6_1_5768 37 49 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 139
  (Polychromatic418967fa.accept_14_8_7_13_1_4113 36 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 139 (accept_3_3 35 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 139 (Polychromatic418967fa.accept_19_14_11_6_1_7151 33 49 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 139 (accept_3_3 32 49 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 139 (Polychromatic418967fa.accept_11_9_5_7_1_815 31 49 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 139 (accept_3_3 29 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 139 (Polychromatic418967fa.accept_16_12_1_11_1_5958 28 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 139 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 49 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 139 (accept_3_3 26 49 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 139 (Polychromatic418967fa.accept_13_12_10_9_1_1166 25 49 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 139
  (Polychromatic418967fa.accept_19_5_11_6_1_1909 24 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 139 (accept_3_3 23 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 139 (Polychromatic418967fa.accept_23_21_3_1_1_7150 21 49 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 139 (accept_3_3 20 49 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 139 (Polychromatic418967fa.accept_13_6_10_9_1_4329 19 49
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 139 (accept_3_3 17 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 139 (Polychromatic418967fa.accept_19_16_11_6_1_7149 16 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 139 (Polychromatic418967fa.accept_14_1_7_13_1_333 15 49 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 139 (accept_3_3 14 49 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 139 (Polychromatic418967fa.accept_19_13_11_6_1_3128 13 49 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 139
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 139 (accept_3_3 11 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 139 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 49 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 139 (accept_3_3 8 49 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 139 (Polychromatic418967fa.accept_24_7_1_19_1_2203 7 49 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 139 (accept_3_3 5 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  139 (Polychromatic418967fa.accept_20_4_9_19_1_766 4 49 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 139 (Polychromatic418967fa.accept_20_3_9_19_1_4214 3 49 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 139 (accept_3_3 2 49 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 139 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 49 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 139)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 139 (allA_succ_of_accept 47 48 139 (accept_3_3 47 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 139 (Polychromatic418967fa.accept_17_11_14_3_1_1427 45 48
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 139 (accept_3_3 44 48 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 43
  48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 139 (accept_3_3 41 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  48 139 (Polychromatic418967fa.accept_14_12_6_13_1_3173 40 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 139 (Polychromatic418967fa.accept_18_3_12_13_1_3307 39 48 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 139 (accept_3_3 38 48 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 48 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 139
  (Polychromatic418967fa.accept_11_3_4_7_1_114 36 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 139 (accept_3_3 35 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 48 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 139 (accept_3_3 32 48 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 139 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 48 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 139
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 139 (accept_3_3 29 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 139 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 48 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 139 (accept_3_3 26 48 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 48 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 139 (accept_3_3 23 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 139 (Polychromatic418967fa.accept_15_7_3_4_1_574 22 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 139 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 48 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 139 (accept_3_3 20 48 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 48 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 139
  (Polychromatic418967fa.accept_21_18_6_13_1_7148 18 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 139 (accept_3_3 17 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 48 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 139 (accept_3_3 14 48 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 139 (Polychromatic418967fa.accept_19_13_10_6_1_7147 13 48 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 139
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 139 (accept_3_3 11 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 139 (Polychromatic418967fa.accept_19_9_10_6_1_4394 9 48 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 139 (accept_3_3 8 48 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 139 (accept_3_3 5 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  139 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 48 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 139 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 139 (accept_3_3 2 48 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 48 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 139)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 139 (allA_of_3_1 47 47 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 139 (allA_succ_of_accept 45 46
  139 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 139 (accept_3_3 44 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 46 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 139 (accept_3_3 41 46 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 46 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 139 (accept_3_3 38 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 139 (Polychromatic418967fa.accept_19_17_8_6_1_7146 36 46 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 139 (accept_3_3 35 46 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 46 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 139 (accept_3_3 32 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 46 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 139 (accept_3_3 29 46 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 46 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 139 (accept_3_3 26 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 46 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 139 (accept_3_3 23 46 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 139 (Polychromatic418967fa.accept_18_4_10_13_1_5883 22 46 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 139 (accept_3_3 20 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 139 (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 46 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 139 (accept_3_3 17 46 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 46 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 139 (accept_3_3 14 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 46 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 139 (accept_3_3 11 46 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 46 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 139 (accept_3_3 8 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  139 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 46 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 139 (accept_3_3 5 46 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 46 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 46
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 139 (accept_3_3 2 46 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  139)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 139 (allA_succ_of_accept 44 45 139 (accept_3_3 44 45
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 139
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 43 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 139 (accept_3_3 41 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 39
  45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 139 (accept_3_3 38 45
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 139 (Polychromatic418967fa.accept_7_2_3_6_1_4
  37 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 139
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 139 (accept_3_3 35 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 139 (Polychromatic418967fa.accept_13_7_6_9_1_1831 33 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 139 (accept_3_3 32 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 139 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 45 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 139 (accept_3_3 29 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 139 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 139 (accept_3_3 26 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 45 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 139
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 139 (accept_3_3 23 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 139 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 139 (accept_3_3 20 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 139 (Polychromatic418967fa.accept_17_2_11_3_1_4654 19 45 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 139 (accept_3_3 17 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 139 (Polychromatic418967fa.accept_12_3_9_7_1_472 15 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 139 (accept_3_3 14 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 139 (Polychromatic418967fa.accept_19_13_7_6_1_5826 13 45 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 139
  (Polychromatic418967fa.accept_21_12_3_13_1_7145 12 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 139 (accept_3_3 11 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 139 (accept_3_3 8 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 139 (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 45 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 139 (accept_3_3 5 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 139 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 139 (accept_3_3 2 45 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 139 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 45 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 139))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  139 (allA_of_3_1 44 44 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 139 (allA_succ_of_accept 42 43 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 139 (accept_3_3 41 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 139 (accept_3_3 38 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 43 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 139
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 139 (accept_3_3 35 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 139 (Polychromatic418967fa.accept_10_4_3_9_1_1262 34 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 139 (accept_3_3 32 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 139 (Polychromatic418967fa.accept_13_5_4_9_1_601 31 43 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 139
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 139 (accept_3_3 29 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 139 (Polychromatic418967fa.accept_17_10_9_3_1_7144 27 43 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 139 (accept_3_3 26 43 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 139 (Polychromatic418967fa.accept_11_3_10_7_1_129 25 43 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 139 (accept_3_3 23 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 139 (Polychromatic418967fa.accept_18_4_7_13_1_3303 22 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 139 (accept_3_3 20 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 43 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 139
  (Polychromatic418967fa.accept_13_5_4_9_1_601 18 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 139 (accept_3_3 17 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 139 (accept_3_3 14 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 139 (Polychromatic418967fa.accept_22_13_21_7_1_7143 13 43 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 139
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 139 (accept_3_3 11 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 139 (accept_3_3 8 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 139 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 43 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 139 (accept_3_3 5 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  139 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 43 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 139 (accept_3_3 2 43 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 139)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 139 (allA_succ_of_accept 41 42 139 (accept_3_3 41 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 139 (Polychromatic418967fa.accept_19_2_4_6_1_5738 40 42 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 42 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 139 (accept_3_3 38 42 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 139
  (Polychromatic418967fa.accept_19_17_4_6_1_5810 36 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 139 (accept_3_3 35 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 139 (accept_3_3 32 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 139 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 42 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 139 (accept_3_3 29 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 139 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 139 (accept_3_3 26 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 139
  (Polychromatic418967fa.accept_11_2_9_7_1_124 24 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 139 (accept_3_3 23 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 139 (Polychromatic418967fa.accept_15_7_12_4_1_1236 22 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 139 (accept_3_3 20 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 42 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 139
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 139 (accept_3_3 17 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 139 (Polychromatic418967fa.accept_13_2_3_9_1_2610 15 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 139 (accept_3_3 14 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 139 (accept_3_3 11 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 139 (accept_3_3 8 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 42 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 139
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 139 (accept_3_3 5 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  139 (Polychromatic418967fa.accept_20_4_2_19_1_7142 4 42 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 42 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 139 (accept_3_3 2 42 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 139))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 41 139 (allA_of_3_1 41 41 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 139
  (allA_succ_of_accept 39 40 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 40 139 (accept_3_3 38 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 40 139 (Polychromatic418967fa.accept_13_11_1_9_1_1179 37 40 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 40 139
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 40 139 (accept_3_3 35 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  40 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 40 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 139 (accept_3_3 32 40 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 40 139 (Polychromatic418967fa.accept_13_5_1_9_1_618 31 40 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 40 139
  (Polychromatic418967fa.accept_22_8_18_7_1_7141 30 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 40 139 (accept_3_3 29 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  40 139 (Polychromatic418967fa.accept_13_2_1_9_1_1174 28 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 40 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 139 (accept_3_3 26 40 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 40 139 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 40 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 40 139
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 40 139 (accept_3_3 23 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  40 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 40 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 40 139 (accept_3_3 20 40 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 40 139 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 40 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 139
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 40 139 (accept_3_3 17 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  40 139 (Polychromatic418967fa.accept_21_16_19_13_1_7140 16 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 40 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 40 139 (accept_3_3 14 40 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 139 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 40 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 139
  (Polychromatic418967fa.accept_16_12_8_11_1_2695 12 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 139 (accept_3_3 11 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  40 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 40 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 139 (accept_3_3 8 40 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 139 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 40 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 139
  (Polychromatic418967fa.accept_13_6_1_9_1_619 6 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 40 139 (accept_3_3 5 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 40
  139 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 40 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 40 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 139 (accept_3_3 2 40 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 40 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 40 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 139)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 139
  (allA_succ_of_accept 38 39 139 (accept_3_3 38 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  39 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 39 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 39 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 139 (accept_3_3 35 39 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 39 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 139
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 139 (accept_3_3 32 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 39 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 139 (accept_3_3 29 39 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 139
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 139 (accept_3_3 26 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 139 (accept_3_3 23 39 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 39 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 139
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 139 (accept_3_3 20 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 139 (Polychromatic418967fa.accept_16_2_7_11_1_1698 18 39 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 139 (accept_3_3 17 39 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 139 (accept_3_3 14 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 139 (Polychromatic418967fa.accept_15_13_9_4_1_3892 13 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 139 (accept_3_3 11 39 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 39 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 139
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 139 (accept_3_3 8 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  139 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 139 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 39 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 139 (accept_3_3 5 39 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  39 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 139 (accept_3_3 2 39 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 39
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  139))))))))))))))))))))))))))))))))))))))) (allB_succ 38 139 (allA_of_3_1 38 38 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 139 (allA_succ_of_accept 36 37 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 139 (accept_3_3 35 37 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 139
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 139 (accept_3_3 32 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 139 (accept_3_3 29 37 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 139 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 37 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 139
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 139 (accept_3_3 26 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 139 (accept_3_3 23 37 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 139
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 139 (accept_3_3 20 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 139 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 139 (accept_3_3 17 37 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 139
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 139 (accept_3_3 14 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 139 (Polychromatic418967fa.accept_22_13_15_7_1_5477 13 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 37 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 139 (accept_3_3 11 37 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 139
  (Polychromatic418967fa.accept_16_9_5_11_1_3776 9 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 139 (accept_3_3 8 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  139 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 139 (accept_3_3 5 37 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 37 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 37
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 139 (accept_3_3 2 37 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 139)))))))))))))))))))))))))))))))))))))
  (allB_succ 36 139 (allA_succ_of_accept 35 36 139 (accept_3_3 35 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 139 (Polychromatic418967fa.accept_23_11_13_1_1_7139 34 36 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 139 (accept_3_3 32 36 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 31
  36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 139
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 139 (accept_3_3 29 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 139 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 139 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 36 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 139 (accept_3_3 26 36 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 139 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 36 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 139
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 139 (accept_3_3 23 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 139 (Polychromatic418967fa.accept_16_6_4_11_1_1719 22 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 139 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 36 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 139 (accept_3_3 20 36 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 36 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 139
  (Polychromatic418967fa.accept_17_1_2_3_1_4668 18 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 139 (accept_3_3 17 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 139 (accept_3_3 14 36 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 139 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 36 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 139
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 139 (accept_3_3 11 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 139 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 139 (accept_3_3 8 36 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 139
  (Polychromatic418967fa.accept_13_6_10_9_1_4329 6 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 139 (accept_3_3 5 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  139 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 36 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 36 139 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 36 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 139 (accept_3_3 2 36 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 36 139 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 36 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 139)))))))))))))))))))))))))))))))))))) (allB_succ 35 139
  (allA_of_3_1 35 35 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 139 (allA_succ_of_accept 33 34 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 139 (accept_3_3 32 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 139 (Polychromatic418967fa.accept_19_12_15_6_1_7138 31 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 34 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 139 (accept_3_3 29 34 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 34 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 139 (accept_3_3 26 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 34 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 139 (accept_3_3 23 34 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 139 (Polychromatic418967fa.accept_16_6_2_11_1_7132 22 34 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 139 (accept_3_3 20 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 139 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 34 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 139 (accept_3_3 17 34 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 34 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 139 (accept_3_3 14 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 34 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 139 (accept_3_3 11 34 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 34 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 139 (accept_3_3 8 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  139 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 34 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 34 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 139 (accept_3_3 5 34 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 34 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 34 139 (accept_3_3 2 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34
  139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 139)))))))))))))))))))))))))))))))))) (allB_succ 33 139 (allA_succ_of_accept 32 33 139 (accept_3_3 32 33
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 139
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 31 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 33 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 139 (accept_3_3 29 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 33 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 139 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 139 (accept_3_3 26
  33 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 139
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 33 139 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 139 (accept_3_3 23 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 33 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 21
  33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 139 (accept_3_3 20 33
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 139 (Polychromatic418967fa.accept_9_1_6_4_1_49
  19 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 139 (accept_3_3 17 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 33 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 139 (accept_3_3 14 33 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 139 (Polychromatic418967fa.accept_17_13_16_3_1_1431 13 33 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 139 (accept_3_3 11 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 139 (Polychromatic418967fa.accept_19_9_14_6_1_2014 9 33 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 139 (accept_3_3 8 33 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 33 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 139 (accept_3_3 5 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 139 (accept_3_3 2 33 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 33 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 139))))))))))))))))))))))))))))))))) (allB_succ 32 139
  (allA_of_3_1 32 32 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 139 (allA_succ_of_accept 30 31 139
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 139 (accept_3_3 29 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 139 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 139 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 31 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 139 (accept_3_3 26 31 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 31 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 139
  (Polychromatic418967fa.accept_11_2_9_7_1_124 24 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 139 (accept_3_3 23 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 139 (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 139 (Polychromatic418967fa.accept_19_2_12_6_1_5816 21 31 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 139 (accept_3_3 20 31 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 139 (Polychromatic418967fa.accept_16_3_15_11_1_2676 19 31
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 139
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 139 (accept_3_3 17 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 139 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 31 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 139 (accept_3_3 14 31 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 139 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 31 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 139
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 139 (accept_3_3 11 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 139 (Polychromatic418967fa.accept_14_10_3_13_1_1530 10 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 31 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 139 (accept_3_3 8 31 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 139 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 31 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 139
  (Polychromatic418967fa.accept_17_6_14_3_1_4678 6 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 139 (accept_3_3 5 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  139 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 31 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 139 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 31 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 139 (accept_3_3 2 31 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 139 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 31 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 139))))))))))))))))))))))))))))))) (allB_succ 30 139
  (allA_succ_of_accept 29 30 139 (accept_3_3 29 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 139 (Polychromatic418967fa.accept_17_10_13_3_1_1425 27 30 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 139 (accept_3_3 26 30 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 139
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 139 (accept_3_3 23 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 139 (accept_3_3 20 30 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 30 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 139
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 139 (accept_3_3 17 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 30 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 139 (accept_3_3 14 30 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 139
  (Polychromatic418967fa.accept_21_12_9_13_1_4091 12 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 139 (accept_3_3 11 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  30 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 30 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 139 (accept_3_3 8 30 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 139 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 30 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 139 (accept_3_3 5 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  139 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 30 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 30 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 30 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 139 (accept_3_3 2 30 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 30 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 139)))))))))))))))))))))))))))))) (allB_succ 29 139 (allA_of_3_1
  29 29 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 139 (allA_succ_of_accept 27 28 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 139 (accept_3_3 26 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 28 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 139 (accept_3_3 23 28 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 28 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 139 (accept_3_3 20 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 139 (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 139 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 28 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 139 (accept_3_3 17 28 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 28 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 139 (accept_3_3 14 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 139 (Polychromatic418967fa.accept_19_13_9_6_1_4393 13 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 28 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 139 (accept_3_3 11 28 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 139 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 28 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 139 (accept_3_3 8 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  139 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 28 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 139 (accept_3_3 5 28 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 139 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 28 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 139 (accept_3_3 2 28 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 139 (Polychromatic418967fa.accept_10_1_8_9_1_787 1
  28 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 139))))))))))))))))))))))))))))
  (allB_succ 27 139 (allA_succ_of_accept 26 27 139 (accept_3_3 26 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 139 (Polychromatic418967fa.accept_21_4_6_13_1_7137 25 27 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 139 (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 27
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 139 (accept_3_3 23 27 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 139
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 139 (accept_3_3 20 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 139 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 139 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 27 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 139 (accept_3_3 17 27 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 139
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 15 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 139 (accept_3_3 14 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 139 (Polychromatic418967fa.accept_17_13_10_3_1_7136 13 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 139 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 27 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 139 (accept_3_3 11 27 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 27 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 139
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 139 (accept_3_3 8 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  139 (Polychromatic418967fa.accept_15_7_12_4_1_1236 7 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 139 (Polychromatic418967fa.accept_13_6_1_9_1_619 6 27 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 139 (accept_3_3 5 27 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 139
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 3 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 139 (accept_3_3 2 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  139 (Polychromatic418967fa.accept_15_1_12_4_1_2022 1 27 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 139))))))))))))))))))))))))))) (allB_succ 26 139 (allA_of_3_1 26 26 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 25 139 (allA_succ_of_accept 24 25 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 24
  25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 139 (accept_3_3 23 25
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 139 (Polychromatic418967fa.accept_4_2_1_3_1_27
  22 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 139
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 139 (accept_3_3 20 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 139 (accept_3_3 17 25 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 139 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 25 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 139 (accept_3_3 14 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 139 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 139 (accept_3_3 11 25 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 139
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 139 (accept_3_3 8 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  139 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 139 (accept_3_3 5 25 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 139 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 25 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 139
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 139 (accept_3_3 2 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  139 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 25 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 139))))))))))))))))))))))))) (allB_succ 24 139 (allA_succ_of_accept 23 24 139 (accept_3_3 23 24 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 139 (Polychromatic418967fa.accept_19_3_5_6_1_7135
  22 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 139
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 24 139 (accept_3_3 20 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  24 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 24 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 24 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 139 (accept_3_3 17 24 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 139 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 24 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 139
  (Polychromatic418967fa.accept_10_5_4_9_1_420 15 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 24 139 (accept_3_3 14 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  24 139 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 24 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 24 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 139 (accept_3_3 11 24 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 24 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 139
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 24 139 (accept_3_3 8 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24
  139 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 24 139 (Polychromatic418967fa.accept_15_6_9_4_1_1227 6 24 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 139 (accept_3_3 5 24 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 24 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 24 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  24 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 139 (accept_3_3 2 24 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 24
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 139)))))))))))))))))))))))) (allB_succ
  23 139 (allA_of_3_1 23 23 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 139 (allA_succ_of_accept 21 22
  139 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 139 (accept_3_3 20 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 139 (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 22 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 139 (accept_3_3 17 22 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 22 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 139 (accept_3_3 14 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 139 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 22 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 139 (accept_3_3 11 22 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 139 (Polychromatic418967fa.accept_15_10_7_4_1_1222 10 22 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 139 (accept_3_3 8 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  139 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 22 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 139 (Polychromatic418967fa.accept_17_6_5_3_1_7134 6 22 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 139 (accept_3_3 5 22 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 139 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 22 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 22
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 139 (accept_3_3 2 22 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 139)))))))))))))))))))))) (allB_succ 21
  139 (allA_succ_of_accept 20 21 139 (accept_3_3 20 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 21 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 139 (accept_3_3 17 21 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 139 (accept_3_3 14 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 139 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 139 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 21 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 139 (accept_3_3 11 21 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 139
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 139 (accept_3_3 8 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  139 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 139 (accept_3_3 5 21 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 139 (Polychromatic418967fa.accept_11_3_10_7_1_129 3
  21 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 139 (accept_3_3 2 21 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 21
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 139))))))))))))))))))))) (allB_succ 20
  139 (allA_of_3_1 20 20 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 139 (allA_succ_of_accept 18 19 139
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 139 (accept_3_3 17 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 19 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 139 (accept_3_3 14 19 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 139 (Polychromatic418967fa.accept_22_13_19_7_1_2558 13 19 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 139
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 139 (accept_3_3 11 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 139 (Polychromatic418967fa.accept_13_10_6_9_1_1152 10 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 139 (Polychromatic418967fa.accept_27_9_19_4_1_7133 9 19 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 139 (accept_3_3 8 19 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 139 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 139
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 139 (accept_3_3 5 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  139 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 19 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 139 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 19 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 139 (accept_3_3 2 19 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 19 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 139))))))))))))))))))) (allB_succ 18 139 (allA_succ_of_accept 17
  18 139 (accept_3_3 17 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 139
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 139 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 18 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 139 (accept_3_3 14 18 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 139 (Polychromatic418967fa.accept_7_5_4_6_1_167 12
  18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 139 (accept_3_3 11 18
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 139
  (Polychromatic418967fa.accept_7_3_4_6_1_329 10 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 18 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 139 (accept_3_3 8 18 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 18 139 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 18 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 139 (Polychromatic418967fa.accept_16_6_2_11_1_7132
  6 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 139 (accept_3_3 5 18
  139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 139
  (Polychromatic418967fa.accept_10_4_8_9_1_784 4 18 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 18 139 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 18 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 139 (accept_3_3 2 18 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 18 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 139)))))))))))))))))) (allB_succ 17 139 (allA_of_3_1 17 17 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 139 (allA_succ_of_accept 15 16 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 139 (accept_3_3 14 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 139 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 16 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 139 (accept_3_3 11 16 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 16 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 139 (accept_3_3 8 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  139 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 16 139 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 16 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 139 (accept_3_3 5 16 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 16 139 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 16 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 16 139 (accept_3_3 2 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16
  139 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 16 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 139)))))))))))))))) (allB_succ 15 139 (allA_succ_of_accept 14 15 139 (accept_3_3 14 15 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 139 (Polychromatic418967fa.accept_19_13_15_6_1_7131 13 15
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 139
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 15 139 (accept_3_3 11 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  15 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 15 139 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 15 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 139 (accept_3_3 8 15 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 139 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 15 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 139
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 139 (accept_3_3 5 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 15 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 139 (accept_3_3 2 15 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 139 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 15 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 139))))))))))))))) (allB_succ 14 139 (allA_of_3_1 14 14 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 139 (allA_succ_of_accept 12 13 139
  (Polychromatic418967fa.accept_19_12_13_6_1_7130 12 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 139 (accept_3_3 11 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 139 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 13 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 139 (accept_3_3 8 13 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 139 (Polychromatic418967fa.accept_19_7_13_6_1_1914 7 13 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 139
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 139 (accept_3_3 5 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  139 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 13 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 139 (Polychromatic418967fa.accept_23_3_13_1_1_7129 3 13 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 139 (accept_3_3 2 13 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 139 (Polychromatic418967fa.accept_24_1_13_19_1_2191 1 13 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 139))))))))))))) (allB_succ 12 139
  (allA_succ_of_accept 11 12 139 (accept_3_3 11 12 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  12 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 12 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 139 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 12 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 139 (accept_3_3 8 12 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 139 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 139
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 12 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 139 (accept_3_3 5 12 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12
  139 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 12 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 12 139 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 12 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 139 (accept_3_3 2 12 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 12 139 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 139)))))))))))) (allB_succ 11 139 (allA_of_3_1 11 11 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 139 (allA_succ_of_accept 9 10 139
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 139 (accept_3_3 8 10 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  139 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 10 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 139 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 10 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 139 (accept_3_3 5 10 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 139 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 10 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 139 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 10
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 139 (accept_3_3 2 10 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 139)))))))))) (allB_succ 9 139
  (allA_succ_of_accept 8 9 139 (accept_3_3 8 9 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 139
  (Polychromatic418967fa.accept_21_7_9_13_1_5612 7 9 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 139 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 139 (accept_3_3 5 9 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 139 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 139 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 9
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 139 (accept_3_3 2 9 139
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 139 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 9
  139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 139))))))))) (allB_succ 8 139
  (allA_of_3_1 8 8 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 139 (allA_succ_of_accept 6 7 139
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 7 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 139 (accept_3_3 5 7 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 139
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 7 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 139 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 7 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 139 (accept_3_3 2 7 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 139 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 139))))))) (allB_succ 6 139 (allA_succ_of_accept 5 6 139
  (accept_3_3 5 6 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 139
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 6 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 139 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 6 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 139 (accept_3_3 2 6 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 139 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 139)))))) (allB_succ 5 139 (allA_of_3_1 5 5 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 139 (allA_succ_of_accept 3 4 139
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 139 (accept_3_3 2 4 139 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 139
  (Polychromatic418967fa.accept_21_1_4_13_1_7128 1 4 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 139)))) (allB_succ 3 139 (allA_succ_of_accept 2 3 139 (accept_3_3 2 3 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 139 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 3 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 139))) (allB_succ 2 139 (allA_of_3_1 2 2 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  139)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


