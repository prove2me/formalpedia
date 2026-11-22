-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch136
-- name    : Polychromatic418967fa_Branch136
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:13:44.977181+00:00
-- url     : https://prove2.me/theorems/e152753a-06a5-42bf-9854-9a0ead9b7110
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

def Polychromatic418967fa.branch_136 : allB 136 136 :=
  allB_succ' 2 135 136 (Eq.refl Bool.true) (allA_succ_of_accept 1 135 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  135 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 136)) (allB_succ' 3 134 136
  (Eq.refl Bool.true) (allA_of_3_1 3 134 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 133 136 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 133 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 133 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 136 (accept_3_3 2 133 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 136 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 133 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 136)))) (allB_succ' 5 132 136 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 132 136 4 1 33 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 132 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 132 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 136 2 1 66 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 136 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 132 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 136))))) (allB_succ' 6 131 136 (Eq.refl
  Bool.true) (allA_of_3_1 6 131 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 130 136 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 130 136 2 3 65 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 130 136 (accept_3_3 5 130 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130
  136 2 2 65 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  130 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 130 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 130 136 2 1 65 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 130 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 130 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 136))))))) (allB_succ' 8 129 136 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 129 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 129 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 129 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 136 (accept_3_3 5 129 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 136 (Polychromatic418967fa.accept_9_4_3_1_1_154 4
  129 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 136
  (Polychromatic418967fa.accept_10_3_9_6_1_94 3 129 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 136 (accept_3_3 2 129 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129 136)))))))) (allB_succ' 9 128 136 (Eq.refl Bool.true) (allA_of_3_1 9 128 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 127 136 (Eq.refl Bool.true) (allA_succ_of_accept 9 127 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 127 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 136 (accept_3_3 8 127 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 136 (Polychromatic418967fa.accept_16_7_15_8_1_278 7 127 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 136 (Polychromatic418967fa.accept_15_6_7_1_1_93 6 127 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 136 (accept_3_3 5 127 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 136 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 127 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 136 (accept_3_3 2 127 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 136 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 127 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 136)))))))))) (allB_succ' 11 126 136 (Eq.refl Bool.true) (allA_succ_of_gcd 10 126 136 2 5 63
  68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 136
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 126 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 136 2 4 63 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 136 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 126 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 136 2 3 63 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 136 (accept_3_3 5 126 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 136 2 2 63 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 126 136 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 126 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 136 2 1 63 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 136 (Polychromatic418967fa.accept_13_1_9_6_1_146 1
  126 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 136))))))))))) (allB_succ' 12 125
  136 (Eq.refl Bool.true) (allA_of_3_1 12 125 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 124 136
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 124 136 4 3 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 124 136 (accept_3_3 11 124 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 124 136 2 5 62 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 124 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 124 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 136 4 2 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 136 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 124 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 136 2 3 62 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 136 (accept_3_3 5 124 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 136 4 1 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 124 136 (Polychromatic418967fa.accept_9_3_7_1_1_143 3
  124 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 136 2 1 62 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 136
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 124 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 124 136))))))))))))) (allB_succ' 14 123 136 (Eq.refl Bool.true) (allA_succ_of_accept 13 123 136
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 123 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 123 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 136 (accept_3_3 11 123 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 123 136 (Polychromatic418967fa.accept_19_10_9_3_1_7009 10 123 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 136
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 123 136 (accept_3_3 8 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  123 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 123 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 123 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 136 (accept_3_3 5 123 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 136 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 123 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 136 (accept_3_3 2 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123 136)))))))))))))) (allB_succ' 15 122 136 (Eq.refl Bool.true) (allA_of_3_1 15 122 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 121 136 (Eq.refl Bool.true) (allA_succ_of_accept 15 121 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 136 (accept_3_3 14 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 121 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 136 (accept_3_3 11 121 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 121 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 136 (accept_3_3 8 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 121 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 136 (accept_3_3 5 121 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 136 (Polychromatic418967fa.accept_16_4_9_8_1_2509 4 121 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 136 (accept_3_3 2 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 136)))))))))))))))) (allB_succ' 17 120 136 (Eq.refl Bool.true) (allA_succ_of_gcd 16 120 136
  8 2 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 120
  136 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 120 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 120 136 2 7 60 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 120 136 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 120 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 136 4 3 30 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 136 (accept_3_3 11 120 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 136 2 5 60 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 136
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 120 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 136 8 1 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 120 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 136 2 3 60 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 136 (accept_3_3 5 120 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 120 136 4 1 30 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 120 136 (Polychromatic418967fa.accept_21_3_15_10_1_3895 3 120 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 136 2 1 60 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 136
  (Polychromatic418967fa.accept_13_1_3_6_1_158 1 120 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 136))))))))))))))))) (allB_succ' 18 119 136 (Eq.refl Bool.true) (allA_of_3_1 18 119 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 118 136 (Eq.refl Bool.true) (allA_succ_of_gcd 18 118 136 2 9 59 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 118 136
  (accept_3_3 17 118 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 118 136 2 8 59 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 118 136
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 118 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 118 136 2 7 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 118 136 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 118 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 136 2 6 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 136 (accept_3_3 11 118 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 136 2 5 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 118 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 118 136 2 4 59 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 136
  (Polychromatic418967fa.accept_11_7_8_4_1_718 7 118 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 136 2 3 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 136 (accept_3_3 5 118 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  136 2 2 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 136 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 118 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 136 2 1 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 118 136 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 118 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 136))))))))))))))))))) (allB_succ' 20 117 136 (Eq.refl
  Bool.true) (allA_succ_of_accept 19 117 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 117 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 136 (Polychromatic418967fa.accept_12_6_9_4_1_96
  18 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 136 (accept_3_3 17
  117 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 136
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 117 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 117 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 136 (accept_3_3 14 117 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 117 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 136
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 136 (accept_3_3 11 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 136 (Polychromatic418967fa.accept_22_10_7_4_1_7008 10 117 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 117 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 136 (accept_3_3 8 117 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 136
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 136 (accept_3_3 5 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 136 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 136 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 117 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 136 (accept_3_3 2 117 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117 136)))))))))))))))))))) (allB_succ' 21 116 136
  (Eq.refl Bool.true) (allA_of_3_1 21 116 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 115 136 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 115 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 115 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 136 (accept_3_3 20 115 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 136 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 115 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 136
  (Polychromatic418967fa.accept_13_5_11_6_1_505 18 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 136 (accept_3_3 17 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 136 (Polychromatic418967fa.accept_19_16_1_3_1_7007 16 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 115 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 136 (accept_3_3 14 115 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 115 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 136
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 136 (accept_3_3 11 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 136 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 115 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 136 (accept_3_3 8 115 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 136 (Polychromatic418967fa.accept_14_7_3_10_1_1364 7 115 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 136 (accept_3_3 5 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 136 (accept_3_3 2 115 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 136 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 115 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 136)))))))))))))))))))))) (allB_succ' 23 114 136
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 114 136 2 11 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 114 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 136 2 10 57 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 136
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 114 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 136 2 9 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 136 (accept_3_3 17 114 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  114 136 2 8 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 114 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 114 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 114 136 2 7 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 114 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 114 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 136 2 6 57 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 136 (accept_3_3 11 114 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 136 2 5 57 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 136
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 114 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 136 2 4 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 114 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 136 2 3 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 136 (accept_3_3 5 114 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 136 2 2 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 114 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 114 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 136 2 1 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  114 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 136)))))))))))))))))))))))
  (allB_succ' 24 113 136 (Eq.refl Bool.true) (allA_of_3_1 24 113 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 25 112 136 (Eq.refl Bool.true) (allA_succ_of_gcd 24 112 136 8 3 14 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 112 136 (accept_3_3 23 112 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 112 136 2 11 56 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 112 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 21
  112 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 136 4 5 28 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 136
  (Polychromatic418967fa.accept_21_19_7_10_1_7006 19 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 112 136 2 9 56 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 112 136 (accept_3_3 17 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 112 136 8 2 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 112 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 112 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 112 136 2 7 56 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 112 136
  (Polychromatic418967fa.accept_18_13_4_10_1_1076 13 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 112 136 4 3 28 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 112 136 (accept_3_3 11 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 112 136 2 5 56 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 112 136 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 112 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 136 8 1 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 112 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 112 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 136 2 3 56 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 136 (accept_3_3 5 112 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112 136 4 1 28 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 112 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 3
  112 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 136 2 1 56 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 136
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 112 136))))))))))))))))))))))))) (allB_succ' 26 111 136 (Eq.refl Bool.true) (allA_succ_of_accept 25 111 136
  (Polychromatic418967fa.accept_6_1_3_4_1_1 25 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 111 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 111 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 136 (accept_3_3 23 111 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 111 136 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 111 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 136
  (Polychromatic418967fa.accept_19_2_16_3_1_7005 21 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 136 (accept_3_3 20 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 111 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 111 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 136 (accept_3_3 17 111 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 111 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 136
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 136 (accept_3_3 14 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 111 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 111 136 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 111 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 136 (accept_3_3 11 111 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 136 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 111
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 136
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 111 136 (accept_3_3 8 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  111 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 111 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 111 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 136 (accept_3_3 5 111 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 111 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 136
  (Polychromatic418967fa.accept_14_3_13_10_1_761 3 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 136 (accept_3_3 2 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111 136)))))))))))))))))))))))))) (allB_succ' 27 110 136 (Eq.refl Bool.true) (allA_of_3_1 27 110
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 109 136 (Eq.refl Bool.true) (allA_succ_of_accept 27 109
  136 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 136 (accept_3_3 26 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 136 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 136 (Polychromatic418967fa.accept_13_11_5_6_1_519 24 109 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 136 (accept_3_3 23 109 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 109 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 136 (accept_3_3 20 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 136 (Polychromatic418967fa.accept_16_3_13_8_1_1594 19 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 136 (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 109 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 136 (accept_3_3 17 109 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 136 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 109
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 136 (accept_3_3 14 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 136 (Polychromatic418967fa.accept_13_12_5_6_1_1050 12 109 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 136 (accept_3_3 11 109 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 109
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 136 (accept_3_3 8 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 136 (Polychromatic418967fa.accept_14_7_11_10_1_2155 7 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 109 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 136 (accept_3_3 5 109 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 136 (Polychromatic418967fa.accept_13_4_5_6_1_3201 4 109 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 136 (accept_3_3 2 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 136)))))))))))))))))))))))))))) (allB_succ' 29 108 136 (Eq.refl Bool.true) (allA_succ_of_gcd
  28 108 136 4 7 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 108 136 (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 108 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 136 2 13 54 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 136
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 25 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 136 4 6 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 136 (accept_3_3 23 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  108 136 2 11 54 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 108 136 (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 108 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 136 4 5 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 136 (Polychromatic418967fa.accept_15_4_3_1_1_487
  19 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 136 2 9 54 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 136
  (accept_3_3 17 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 136 4 4 27 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 136
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 15 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 108 136 2 7 54 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 108 136 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 108 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 136 4 3 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 136 (accept_3_3 11 108 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 136 2 5 54 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 136 (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 108 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 136 4 2 27 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 136
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 108 136 2 3 54 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 108 136 (accept_3_3 5 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108
  136 4 1 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  108 136 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 108 136 2 1 54 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 108 136 (Polychromatic418967fa.accept_16_1_12_8_1_2405 1 108 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108 136))))))))))))))))))))))))))))) (allB_succ' 30 107 136
  (Eq.refl Bool.true) (allA_of_3_1 30 107 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 106 136 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 106 136 2 15 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 106 136 (accept_3_3 29 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 136 2 14 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 136 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 106 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 136 2 13 53 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 136
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 136 2 12 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 136 (accept_3_3 23 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 136 2 11 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 136 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 106 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 136 2 10 53 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 136
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 136 2 9 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 136 (accept_3_3 17 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 136 2 8 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 136 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 136 2 7 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 106 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 136 2 6 53 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 136 (accept_3_3 11 106 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 136 2 5 53 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 136
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 136 2 4 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 136 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 106 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 136 2 3 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 136 (accept_3_3 5 106 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 136 2 2 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 136 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 106 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 136 2 1 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 136)))))))))))))))))))))))))))))))
  (allB_succ' 32 105 136 (Eq.refl Bool.true) (allA_succ_of_accept 31 105 136 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 136 (accept_3_3 29 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 136 (Polychromatic418967fa.accept_13_2_1_6_1_2365 28 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 136 (Polychromatic418967fa.accept_18_9_15_10_1_395 27 105 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 136 (accept_3_3 26 105 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 105 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 136
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 136 (accept_3_3 23 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 136 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 105 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 136 (accept_3_3 20 105 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 105 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 136
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 136 (accept_3_3 17 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 136 (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 105 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 136 (accept_3_3 14 105 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 136 (accept_3_3 11 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 136 (Polychromatic418967fa.accept_20_10_5_16_1_7004 10 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 136 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 105 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 136 (accept_3_3 8 105 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 105 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 136
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 136 (accept_3_3 5 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 136 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 105 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 136 (accept_3_3 2 105 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 136)))))))))))))))))))))))))))))))) (allB_succ' 33
  104 136 (Eq.refl Bool.true) (allA_of_3_1 33 104 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 103 136
  (Eq.refl Bool.true) (allA_succ_of_accept 33 103 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 103 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 136 (accept_3_3 32 103 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 136 (Polychromatic418967fa.accept_13_5_12_6_1_508 31 103
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 136
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 136 (accept_3_3 29 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 136 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 136 (accept_3_3 26 103 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 103 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 136
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 136 (accept_3_3 23 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 103 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 136 (accept_3_3 20 103 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 136 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 103 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 136
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 136 (accept_3_3 17 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 136 (accept_3_3 14 103 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 136 (Polychromatic418967fa.accept_19_13_8_3_1_2906 13 103 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 136
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 136 (accept_3_3 11 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 103 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 136 (accept_3_3 8 103 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 103 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 136
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 136 (accept_3_3 5 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 136 (Polychromatic418967fa.accept_16_4_7_8_1_5753 4 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 136 (accept_3_3 2 103 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 103 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 136)))))))))))))))))))))))))))))))))) (allB_succ' 35
  102 136 (Eq.refl Bool.true) (allA_succ_of_gcd 34 102 136 34 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 102 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 136 2 16 51 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 136
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 136 2 15 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 136 (accept_3_3 29 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 136 2 14 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 102 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 136 2 13 51 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 136
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 136 2 12 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 136 (accept_3_3 23 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 136 2 11 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 136 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 102 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 136 2 10 51 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 136
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 136 2 9 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 17 102 136 17 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 16 102 136 2 8 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 102 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 102 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 136 2 7 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 13
  102 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 136 2 6 51 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 136 (accept_3_3 11
  102 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 136 2 5 51 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 136
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 136 2 4 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 102 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 136 2 3 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 136 (accept_3_3 5 102 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 136 2 2 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 136 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 102 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 136 2 1 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 1
  102 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  136))))))))))))))))))))))))))))))))))) (allB_succ' 36 101 136 (Eq.refl Bool.true) (allA_of_3_1 36 101 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 100 136 (Eq.refl Bool.true) (allA_succ_of_gcd 36 100 136 4 9 25 34
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 100 136
  (accept_3_3 35 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 100 136 2 17 50 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 100 136
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 100 136 4 8 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 100 136 (Polychromatic418967fa.accept_16_15_4_8_1_1562 31 100 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 136 2 15 50 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 136 (accept_3_3 29 100 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 136 4 7 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 100 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 136 2 13 50 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 136
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 25 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 100 136 4 6 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 100 136 (accept_3_3 23 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  100 136 2 11 50 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 100 136 (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 100 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 136 4 5 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 19
  100 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 136 2 9 50 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 136 (accept_3_3 17
  100 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 136 4 4 25 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 100 136
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 100 136 2 7 50 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 100 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 100 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 136 4 3 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 136 (accept_3_3 11 100 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 136 2 5 50 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 136 (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 100 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 136 4 2 25 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 136
  (Polychromatic418967fa.accept_13_7_9_6_1_148 7 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 100 136 2 3 50 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 100 136 (accept_3_3 5 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100
  136 4 1 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  100 136 (Polychromatic418967fa.accept_13_3_9_6_1_502 3 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 100 136 2 1 50 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 100 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 100 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 136))))))))))))))))))))))))))))))))))))) (allB_succ' 38 99 136
  (Eq.refl Bool.true) (allA_succ_of_accept 37 99 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 99 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 136
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 99 136 (accept_3_3 35 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  99 136 (Polychromatic418967fa.accept_22_12_11_4_1_7003 34 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 99 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 136 (accept_3_3 32 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 136
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 99 136 (accept_3_3 29 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  99 136 (Polychromatic418967fa.accept_13_2_8_6_1_2390 28 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 99 136 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 136 (accept_3_3 26 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 99 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 136
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 99 136 (accept_3_3 23 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  99 136 (Polychromatic418967fa.accept_15_7_9_1_1_473 22 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 99 136 (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 136 (accept_3_3 20 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 136
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 99 136 (accept_3_3 17 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  99 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 99 136 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 136 (accept_3_3 14 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 99 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 136
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 99 136 (accept_3_3 11 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  99 136 (Polychromatic418967fa.accept_15_10_9_1_1_3688 10 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 99 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 136 (accept_3_3 8 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 136
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 136 (accept_3_3 5 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  136 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 99 136 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 99 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 136 (accept_3_3 2 99 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 99 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 136)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 98 136
  (Eq.refl Bool.true) (allA_of_3_1 39 98 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 97 136 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 97 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 136 (accept_3_3 38 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 97 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 136
  (Polychromatic418967fa.accept_15_6_7_1_1_93 36 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 136 (accept_3_3 35 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 136 (accept_3_3 32 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 97 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 136
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 136 (accept_3_3 29 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 136 (Polychromatic418967fa.accept_16_12_1_8_1_5767 28 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 136 (accept_3_3 26 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 97 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 136 (accept_3_3 23 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 136 (accept_3_3 20 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 136 (Polychromatic418967fa.accept_20_19_17_16_1_2732 19 97 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 136
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 136 (accept_3_3 17 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 136 (accept_3_3 14 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 97 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 136
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 136 (accept_3_3 11 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 136 (accept_3_3 8 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 136 (Polychromatic418967fa.accept_16_7_1_8_1_5796 7 97 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 136 (accept_3_3 5 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  136 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 97 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 136 (accept_3_3 2 97 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 136 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 136)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 96
  136 (Eq.refl Bool.true) (allA_succ_of_gcd 40 96 136 8 5 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 96 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 136 2 19 48 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 136
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 136 4 9 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 96 136 (accept_3_3 35 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96
  136 2 17 48 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  96 136 (Polychromatic418967fa.accept_14_5_12_10_1_2985 33 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 96 136 8 4 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 96 136 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 96 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 136 2 15 48 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 136 (accept_3_3 29 96 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 136 4 7 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 136 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 96 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 136 2 13 48 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 136
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 136 8 3 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 136 (accept_3_3 23 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96
  136 2 11 48 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  96 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 96 136 4 5 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 96 136 (Polychromatic418967fa.accept_14_5_12_10_1_2985 19 96 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 136 2 9 48 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 136 (accept_3_3 17 96 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 136 8 2 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 136 2 7 48 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 136
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 136 4 3 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 136 (accept_3_3 11 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96
  136 2 5 48 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  96 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 96 136 8 1 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 96 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 136 2 3 48 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 136 (accept_3_3 5 96 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 136 4 1 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 96 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 96 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 136 2 1 48 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 136
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 136))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 95 136 (Eq.refl Bool.true) (allA_of_3_1 42 95
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 94 136 (Eq.refl Bool.true) (allA_succ_of_gcd 42 94 136 2
  21 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 94
  136 (accept_3_3 41 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94 136 2 20 47 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 94 136
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 94 136 2 19 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 94 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 94 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 94 136 2 18 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 94 136 (accept_3_3 35 94 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94 136 2 17 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 94 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 94 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 136 2 16 47 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 136
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 136 2 15 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 94 136 (accept_3_3 29 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94
  136 2 14 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  94 136 (Polychromatic418967fa.accept_13_1_3_6_1_158 27 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 94 136 2 13 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 94 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 94 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 136 2 12 47 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 136 (accept_3_3 23 94 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 136 2 11 47 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 136
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 94 136 2 10 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 94 136 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 94 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 136 2 9 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 136 (accept_3_3 17 94 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 94 136 2 8 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 94 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 94 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 136 2 7 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 136 (Polychromatic418967fa.accept_11_2_6_4_1_3028
  13 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 136 2 6 47 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 136 (accept_3_3 11
  94 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 136 2 5 47 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 136
  (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 136 2 4 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 94 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 136 2 3 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 136 (accept_3_3 5 94 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 136 2 2 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 94 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 136 2 1 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  136))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 93 136 (Eq.refl Bool.true) (allA_succ_of_accept 43 93
  136 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 93 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 136 (accept_3_3 41 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 93 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 93 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 136 (Polychromatic418967fa.accept_10_9_3_6_1_686
  39 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 136 (accept_3_3 38
  93 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 136
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 93 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 136 (accept_3_3 35 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 93 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 93 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 33
  93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 136 (accept_3_3 32 93
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 136 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 136
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 136 (accept_3_3 29 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  93 136 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 93 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 136 (accept_3_3 26 93 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 136
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 136 (accept_3_3 23 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  93 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 136 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 93 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 136 (accept_3_3 20 93 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 93 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 136
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 136 (accept_3_3 17 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  93 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 93 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 136 (accept_3_3 14 93 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 136
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 93 136 (accept_3_3 11 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  93 136 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 93 136 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 93 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 136 (accept_3_3 8 93 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 93 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 136
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 136 (accept_3_3 5 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  136 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 136 (Polychromatic418967fa.accept_16_3_13_8_1_1594 3 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 136 (accept_3_3 2 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 136)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  92 136 (Eq.refl Bool.true) (allA_of_3_1 45 92 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 91 136
  (Eq.refl Bool.true) (allA_succ_of_accept 45 91 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 91 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 136 (accept_3_3 44 91 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 136 (Polychromatic418967fa.accept_21_1_7_10_1_2596 43 91
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 136
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 136 (accept_3_3 41 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 136 (Polychromatic418967fa.accept_11_7_3_4_1_729 40 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 136 (accept_3_3 38 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 136 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 91 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 136
  (Polychromatic418967fa.accept_16_4_11_8_1_1574 36 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 136 (accept_3_3 35 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 136 (accept_3_3 32 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 136 (Polychromatic418967fa.accept_14_3_7_10_1_2146 31 91 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 136
  (Polychromatic418967fa.accept_21_9_7_10_1_3907 30 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 136 (accept_3_3 29 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 136 (Polychromatic418967fa.accept_16_12_11_8_1_832 28 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 136 (accept_3_3 26 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 136 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 91 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 136
  (Polychromatic418967fa.accept_21_3_7_10_1_7002 24 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 136 (accept_3_3 23 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 136 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 136 (accept_3_3 20 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 136 (Polychromatic418967fa.accept_16_3_11_8_1_830 19 91 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 136
  (Polychromatic418967fa.accept_11_7_3_4_1_729 18 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 136 (accept_3_3 17 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 136 (Polychromatic418967fa.accept_18_16_1_10_1_2029 16 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 136 (accept_3_3 14 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 136 (Polychromatic418967fa.accept_16_13_11_8_1_2449 13 91 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 136
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 136 (accept_3_3 11 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 136 (accept_3_3 8 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 136 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 91 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 136
  (Polychromatic418967fa.accept_20_6_11_16_1_3992 6 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 136 (accept_3_3 5 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  136 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 136 (accept_3_3 2 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 136 (Polychromatic418967fa.accept_20_1_11_16_1_699 1 91 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 136))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 90 136 (Eq.refl Bool.true) (allA_succ_of_gcd 46 90 136 2 23 45 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 136
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 136 2 22 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 90 136 (Polychromatic418967fa.accept_19_5_14_3_1_4187 43 90 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 136 2 21 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 136 (accept_3_3 41 90 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 136 2 20 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 90 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 136 2 19 45 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 136
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 136 2 18 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 136 (accept_3_3 35 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90
  136 2 17 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  90 136 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 90 136 2 16 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 90 136 (Polychromatic418967fa.accept_11_9_2_4_1_707 31 90 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 136 2 15 45 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 136 (accept_3_3 29 90 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 136 2 14 45 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 136
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 136 2 13 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 90 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 90 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 136 2 12 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 136 (accept_3_3 23 90 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 136 2 11 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 136 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 90 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 136 2 10 45 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 136
  (Polychromatic418967fa.accept_20_19_10_16_1_7001 19 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 90 136 2 9 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 90 136 (accept_3_3 17 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 90 136 2 8 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 90 136 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 90 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 136 2 7 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 136 (Polychromatic418967fa.accept_22_13_2_4_1_7000 13 90 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 136 2 6 45 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 136 (accept_3_3 11 90 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 136 2 5 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 90
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 136 2 4 45 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 136
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 136 2 3 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 90 136 (accept_3_3 5 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 136
  2 2 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90
  136 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 136 2 1 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 136 (Polychromatic418967fa.accept_25_1_15_11_1_6999 1 90 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90 136))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 89 136
  (Eq.refl Bool.true) (allA_of_3_1 48 89 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 88 136 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 88 136 8 6 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 88 136 (accept_3_3 47 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 88 136 2 23 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 88 136 (Polychromatic418967fa.accept_19_7_12_3_1_4169 45 88 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 88 136 4 11 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 88 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 43
  88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 136 2 21 44 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 136 (accept_3_3 41
  88 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 136 8 5 11 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 136
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 88 136 2 19 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 88 136 (Polychromatic418967fa.accept_18_1_16_10_1_2065 37 88 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 88 136 4 9 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 88 136 (accept_3_3 35 88 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 88 136 2 17 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 88 136 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 88 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 88 136 8 4 11 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 88 136
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 88 136 2 15 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 88 136 (accept_3_3 29 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88
  136 4 7 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  88 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 88 136 2 13 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 88 136 (Polychromatic418967fa.accept_13_12_10_6_1_3212 25 88 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 136 8 3 11 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 136 (accept_3_3 23 88 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 136 2 11 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 136 (Polychromatic418967fa.accept_9_3_7_1_1_143 21
  88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 136 4 5 22 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 136
  (Polychromatic418967fa.accept_18_1_16_10_1_2065 19 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 136 2 9 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 136 (accept_3_3 17 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  136 8 2 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 136 2 7 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 88 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 88 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 136 4 3 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 136 (accept_3_3 11 88 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 136 2 5 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 88 136 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 88 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 136 8 1 11 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 136
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 7 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 136 2 3 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 136 (accept_3_3 5 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 136
  4 1 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  136 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 88 136 2 1 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 88 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 88 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 88 136))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 87
  136 (Eq.refl Bool.true) (allA_succ_of_accept 49 87 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 87 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 87 136 (accept_3_3 47 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  87 136 (Polychromatic418967fa.accept_13_7_9_6_1_148 46 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 87 136 (Polychromatic418967fa.accept_18_9_15_10_1_395 45 87 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 136 (accept_3_3 44 87 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 136
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 87 136 (accept_3_3 41 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  87 136 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 87 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 136 (accept_3_3 38 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 87 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 136
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 87 136 (accept_3_3 35 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  87 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 87 136 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 136 (accept_3_3 32 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 87 136 (accept_3_3 29 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  87 136 (Polychromatic418967fa.accept_13_2_9_6_1_501 28 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 87 136 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 87 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 136 (accept_3_3 26 87 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 87 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 136
  (Polychromatic418967fa.accept_18_6_15_10_1_6975 24 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 87 136 (accept_3_3 23 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  87 136 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 87 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 136 (accept_3_3 20 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 136
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 87 136 (accept_3_3 17 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  87 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 87 136 (Polychromatic418967fa.accept_13_2_9_6_1_501 15 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 136 (accept_3_3 14 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 87 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 87 136 (accept_3_3 11 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  87 136 (Polychromatic418967fa.accept_13_10_9_6_1_1026 10 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 87 136 (Polychromatic418967fa.accept_16_9_7_8_1_1588 9 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 136 (accept_3_3 8 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 136
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 136 (accept_3_3 5 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87
  136 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 87 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 87 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 136 (accept_3_3 2 87 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 87 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 136))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 86 136 (Eq.refl Bool.true) (allA_of_3_1 51 86 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  52 85 136 (Eq.refl Bool.true) (allA_succ_of_gcd 51 85 136 17 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 85 136 (accept_3_3 50 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 85 136 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 48
  85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 136 (accept_3_3 47 85
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 136
  (Polychromatic418967fa.accept_7_4_1_3_1_277 46 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 85 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 136 (accept_3_3 44 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 85 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 42
  85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 136 (accept_3_3 41 85
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 136
  (Polychromatic418967fa.accept_7_5_1_3_1_103 40 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 85 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 136 (accept_3_3 38 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 85 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 136 (Polychromatic418967fa.accept_15_6_10_1_1_3675
  36 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 136 (accept_3_3 35
  85 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 85 136 17 2 5 8 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 85 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 136 (accept_3_3 32 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 136 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 136 (accept_3_3 29 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 136 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 85 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 136 (accept_3_3 26 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 136 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 136 (accept_3_3 23 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 85 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 136 (accept_3_3 20 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 136 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 85 136 17 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 85 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 16
  85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 136 (accept_3_3 14 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 136 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 136 (accept_3_3 11 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 85 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 136 (accept_3_3 8 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  136 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 85 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 136 (accept_3_3 5 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 85 136 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 85
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 136 (accept_3_3 2 85 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 136 (Polychromatic418967fa.accept_10_1_5_6_1_649 1
  85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  136)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 84 136 (Eq.refl Bool.true) (allA_succ_of_gcd 52
  84 136 4 13 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  51 84 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 84 136 2 25 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 84 136 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 84 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 136 4 12 21 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 136 (accept_3_3 47 84 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 136 2 23 42 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 136
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 84 136 4 11 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 84 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 84 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 136 2 21 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 136 (accept_3_3 41 84 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 136 4 10 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 136 (Polychromatic418967fa.accept_16_7_4_8_1_2487 39 84 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 136 2 19 42 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 136
  (Polychromatic418967fa.accept_15_7_9_1_1_473 37 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 136 4 9 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 136 (accept_3_3 35 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84
  136 2 17 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  84 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 84 136 4 8 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 84 136 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 84 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 136 2 15 42 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 136 (accept_3_3 29 84 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 136 4 7 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 136 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 84 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 136 2 13 42 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 136
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 136 4 6 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 136 (accept_3_3 23 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84
  136 2 11 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  84 136 (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 84 136 4 5 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 84 136 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 84 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 136 2 9 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 136 (accept_3_3 17 84 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 136 4 4 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 84 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 84 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 136 2 7 42 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 136
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 136 4 3 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 136 (accept_3_3 11 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84
  136 2 5 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  84 136 (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 84 136 4 2 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 84 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 84 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 136 2 3 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 136 (accept_3_3 5 84 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 136 4 1 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 84 136 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 84 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 136 2 1 42 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 136
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 136))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 83 136 (Eq.refl Bool.true)
  (allA_of_3_1 54 83 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 82 136 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 82 136 2 27 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 82 136 (accept_3_3 53 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82
  136 2 26 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  82 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 82 136 2 25 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 82 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 82 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 82 136 2 24 41 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 82 136 (accept_3_3 47 82 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82 136 2 23 41 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 82 136
  (Polychromatic418967fa.accept_19_7_6_3_1_6998 45 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 82 136 2 22 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 82 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 82 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 82 136 2 21 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82 136 (accept_3_3 41 82 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 136 2 20 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 136 (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 82 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 136 2 19 41 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 136
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 136 2 18 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 82 136 (accept_3_3 35 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82
  136 2 17 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  82 136 (Polychromatic418967fa.accept_13_7_4_6_1_3221 33 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 82 136 2 16 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 82 136 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 82 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 136 2 15 41 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 136 (accept_3_3 29 82 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 136 2 14 41 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 136
  (Polychromatic418967fa.accept_19_8_6_3_1_4164 27 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 82 136 2 13 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 82 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 82 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 136 2 12 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 136 (accept_3_3 23 82 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 136 2 11 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 136 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 82 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 136 2 10 41 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 136
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 136 2 9 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 136 (accept_3_3 17 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  136 2 8 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 136 2 7 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 82 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 82 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 136 2 6 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 136 (accept_3_3 11 82 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 136 2 5 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 82 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 82 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 82 136 2 4 41 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 82 136
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 82 136 2 3 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 82 136 (accept_3_3 5 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 136
  2 2 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 82
  136 (Polychromatic418967fa.accept_24_3_10_16_1_6997 3 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 82 136 2 1 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 82 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 82 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 136)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 81 136 (Eq.refl Bool.true) (allA_succ_of_accept 55 81 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 55
  81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 136
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 81 136 (accept_3_3 53 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  81 136 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 81 136 (Polychromatic418967fa.accept_18_15_9_10_1_1082 51 81 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 136 (accept_3_3 50 81 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 136
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 81 136 (accept_3_3 47 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  81 136 (Polychromatic418967fa.accept_19_8_5_3_1_4181 46 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 81 136 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 136 (accept_3_3 44 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 81 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 136
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 81 136 (accept_3_3 41 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  81 136 (Polychromatic418967fa.accept_13_1_3_6_1_158 40 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 81 136 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 136 (accept_3_3 38 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 136
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 81 136 (accept_3_3 35 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  81 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 81 136 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 136 (accept_3_3 32 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 81 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 136
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 81 136 (accept_3_3 29 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  81 136 (Polychromatic418967fa.accept_16_12_1_8_1_5767 28 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 81 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 136 (accept_3_3 26 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 136
  (Polychromatic418967fa.accept_15_9_6_1_1_493 24 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 81 136 (accept_3_3 23 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  81 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 81 136 (Polychromatic418967fa.accept_14_7_11_10_1_2155 21 81 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 136 (accept_3_3 20 81 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 81 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 136
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 81 136 (accept_3_3 17 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  81 136 (Polychromatic418967fa.accept_19_16_5_3_1_1813 16 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 81 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 136 (accept_3_3 14 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 136
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 81 136 (accept_3_3 11 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  81 136 (Polychromatic418967fa.accept_13_10_3_6_1_1003 10 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 81 136 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 136 (accept_3_3 8 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 81 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 136
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 136 (accept_3_3 5 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81
  136 (Polychromatic418967fa.accept_16_4_1_8_1_835 4 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 81 136 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 81 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 136 (accept_3_3 2 81 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 81 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 136))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 80 136 (Eq.refl Bool.true) (allA_of_3_1 57 80 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  58 79 136 (Eq.refl Bool.true) (allA_succ_of_accept 57 79 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 79 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 136 (accept_3_3 56 79 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 55
  79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 136
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 136 (accept_3_3 53 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 136 (Polychromatic418967fa.accept_16_4_15_8_1_2413 52 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 136 (accept_3_3 50 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 79 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 136
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 136 (accept_3_3 47 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 136 (accept_3_3 44 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 79 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 136 (accept_3_3 41 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 136 (accept_3_3 38 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 136 (Polychromatic418967fa.accept_20_17_19_16_1_6996 37 79 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 136
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 136 (accept_3_3 35 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 136 (accept_3_3 32 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 79 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 136
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 136 (accept_3_3 29 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 136 (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 136 (accept_3_3 26 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 136 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 79 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 136 (accept_3_3 23 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 136 (accept_3_3 20 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 79 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 136
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 136 (accept_3_3 17 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 136 (Polychromatic418967fa.accept_13_3_1_6_1_509 16 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 136 (accept_3_3 14 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 79 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 136
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 136 (accept_3_3 11 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 136 (accept_3_3 8 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 136 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 79 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 136
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 136 (accept_3_3 5 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  136 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 136 (accept_3_3 2 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 136))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 78 136 (Eq.refl Bool.true) (allA_succ_of_gcd 58 78 136 2 29 39 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 136 2 28 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 78 136 (Polychromatic418967fa.accept_19_17_2_3_1_4190 55 78 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 136 2 27 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 136 (accept_3_3 53 78 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 136 2 26 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 78 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 136 2 25 39 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 136
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 136 2 24 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 78 136 (accept_3_3 47 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78
  136 2 23 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  78 136 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 78 136 2 22 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 78 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 78 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 136 2 21 39 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 136 (accept_3_3 41 78 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 136 2 20 39 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 136
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 136 2 19 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 78 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 78 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 136 2 18 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 136 (accept_3_3 35 78 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 136 2 17 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 78 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 136 2 16 39 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 136
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 136 2 15 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 136 (accept_3_3 29 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78
  136 2 14 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  78 136 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 78 136 2 13 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 78 136 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 78 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 136 2 12 39 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 136 (accept_3_3 23 78 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 136 2 11 39 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 136 2 10 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 78 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 78 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 136 2 9 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 136 (accept_3_3 17 78 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 78 136 2 8 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 78 136 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 78 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 136 2 7 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 136 (Polychromatic418967fa.accept_9_4_6_1_1_393 13
  78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 136 2 6 39 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 136 (accept_3_3 11
  78 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 136 2 5 39 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 136
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 136 2 4 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 78 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 136 2 3 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 136 (accept_3_3 5 78 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 136 2 2 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 78 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 136 2 1 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 136 (Polychromatic418967fa.accept_19_1_2_3_1_6995 1
  78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  136))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 77 136 (Eq.refl Bool.true) (allA_of_3_1
  60 77 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 76 136 (Eq.refl Bool.true) (allA_succ_of_gcd 60 76
  136 4 15 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  76 136 (accept_3_3 59 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 136 2 29 38 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 136
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 76 136 4 14 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 136 (Polychromatic418967fa.accept_16_7_12_8_1_2450 55 76 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 136 2 27 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 136 (accept_3_3 53 76 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 136 4 13 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 76 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 136 2 25 38 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 136
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 49 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 136 4 12 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 136 (accept_3_3 47 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  136 2 23 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  76 136 (Polychromatic418967fa.accept_14_3_6_10_1_752 45 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 136 4 11 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 76 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 136 2 21 38 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 136 (accept_3_3 41 76 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 136 4 10 19 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 136
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 136 2 19 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 76 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 136 4 9 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 136 (accept_3_3 35 76 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 76 136 2 17 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 76 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 76 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 136 4 8 19 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 136
  (Polychromatic418967fa.accept_13_5_11_6_1_505 31 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 136 2 15 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 136 (accept_3_3 29 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  136 4 7 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 136 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 136 2 13 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 76 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 136 4 6 19 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 136 (accept_3_3 23 76 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 136 2 11 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 21
  76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 136 4 5 19 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 136
  (Polychromatic418967fa.accept_16_3_12_8_1_808 19 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 136 2 9 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 136 (accept_3_3 17 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  136 4 4 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 136 2 7 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 76 136 (Polychromatic418967fa.accept_16_13_12_8_1_2451 13 76 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 136 4 3 19 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 136 (accept_3_3 11 76 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 136 2 5 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 76 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 136 4 2 19 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 136
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 136 2 3 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 136 (accept_3_3 5 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 136
  4 1 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  136 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 136 2 1 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 136 (Polychromatic418967fa.accept_16_1_12_8_1_2405 1 76 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76 136)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 75 136 (Eq.refl Bool.true) (allA_succ_of_accept 61 75 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 61
  75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 136
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 75 136 (accept_3_3 59 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  75 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 75 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 136 (accept_3_3 56 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 75 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 136
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 136 (accept_3_3 53 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 136 (accept_3_3 50 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 75 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 136
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 48 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 136 (accept_3_3 47 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  75 136 (Polychromatic418967fa.accept_11_2_9_4_1_310 46 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 136 (Polychromatic418967fa.accept_16_13_11_8_1_2449 45 75 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 136 (accept_3_3 44 75 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 136
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 136 (accept_3_3 41 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 136 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 136 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 136 (accept_3_3 38 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 75 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 136
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 136 (accept_3_3 35 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 136 (accept_3_3 32 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 136
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 136 (accept_3_3 29 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 136 (Polychromatic418967fa.accept_13_2_10_6_1_1676 28 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 136 (Polychromatic418967fa.accept_21_6_12_10_1_2576 27 75 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 136 (accept_3_3 26 75 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 75 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 136
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 136 (accept_3_3 23 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 136 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 136 (accept_3_3 20 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 136
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 136 (accept_3_3 17 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 136 (accept_3_3 14 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 75 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 136
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 136 (accept_3_3 11 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 136 (Polychromatic418967fa.accept_20_10_15_16_1_6994 10 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 136 (accept_3_3 8 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 136
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 136 (accept_3_3 5 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  136 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 136 (Polychromatic418967fa.accept_13_3_10_6_1_2382 3 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 136 (accept_3_3 2 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  136)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 74 136 (Eq.refl Bool.true)
  (allA_of_3_1 63 74 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 73 136 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 73 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 136 (accept_3_3 62 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 73 136 (Polychromatic418967fa.accept_19_4_16_3_1_4175 61 73 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 136
  (Polychromatic418967fa.accept_16_12_9_8_1_2508 60 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 136 (accept_3_3 59 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 136 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 136 (accept_3_3 56 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 136 (Polychromatic418967fa.accept_14_13_3_10_1_2159 55 73 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 136
  (Polychromatic418967fa.accept_13_2_8_6_1_2390 54 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 136 (accept_3_3 53 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 136 (Polychromatic418967fa.accept_11_8_7_4_1_3011 52 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 136 (accept_3_3 50 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 136 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 73 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 136
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 136 (accept_3_3 47 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 136 (accept_3_3 44 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 136 (Polychromatic418967fa.accept_19_5_16_3_1_1820 43 73 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 136
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 136 (accept_3_3 41 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 136 (Polychromatic418967fa.accept_13_1_8_6_1_1016 40 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 136 (accept_3_3 38 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 136 (Polychromatic418967fa.accept_10_7_3_6_1_644 37 73 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 136
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 136 (accept_3_3 35 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 136 (accept_3_3 32 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 136 (Polychromatic418967fa.accept_16_15_9_8_1_2440 31 73 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 136
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 136 (accept_3_3 29 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 136 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 136 (accept_3_3 26 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 136 (Polychromatic418967fa.accept_11_3_7_4_1_1133 25 73 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 136
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 136 (accept_3_3 23 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 136 (accept_3_3 20 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 136 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 73 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 136
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 136 (accept_3_3 17 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 136 (Polychromatic418967fa.accept_18_16_1_10_1_2029 16 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 136 (accept_3_3 14 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 136 (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 73 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 136
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 12 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 136 (accept_3_3 11 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 136 (accept_3_3 8 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 136 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 73 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 136
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 136 (accept_3_3 5 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  136 (Polychromatic418967fa.accept_16_4_9_8_1_2509 4 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 136 (accept_3_3 2 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 136 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 73 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  136)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 72 136 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 72 136 8 8 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 72 136 (Polychromatic418967fa.accept_27_9_18_1_1_6993 63 72 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 136 2 31 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 61
  72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 136 4 15 18 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 136 (accept_3_3 59
  72 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 136 2 29 36 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 136
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 72 136 8 7 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 72 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 72 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 136 2 27 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 136 (accept_3_3 53 72 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 136 4 13 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 136 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 72 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 136 2 25 36 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 136
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 72 136 8 6 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 72 136 (accept_3_3 47 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72
  136 2 23 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  72 136 (Polychromatic418967fa.accept_19_7_15_3_1_2896 45 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 72 136 4 11 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 72 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 72 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 136 2 21 36 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 136 (accept_3_3 41 72 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 136 8 5 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 72 136 (Polychromatic418967fa.accept_21_18_9_10_1_2571
  39 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 136 2 19 36 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 136
  (Polychromatic418967fa.accept_19_18_15_3_1_5548 37 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 136 4 9 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 136 (accept_3_3 35 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72
  136 2 17 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  72 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 72 136 8 4 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 72 136 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 72 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 136 2 15 36 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 136 (accept_3_3 29 72 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 136 4 7 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 136 2 13 36 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 136
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 25 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 136 8 3 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 136 (accept_3_3 23 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72
  136 2 11 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  72 136 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 136 4 5 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 72 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 136 2 9 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 136 (accept_3_3 17 72 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 136 8 2 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 72 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 136 2 7 36 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 136
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 136 4 3 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 136 (accept_3_3 11 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72
  136 2 5 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  72 136 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 72 136 8 1 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 72 136 (Polychromatic418967fa.accept_19_7_15_3_1_2896 7 72 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 136 2 3 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 136 (accept_3_3 5 72 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 136 4 1 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 72 136 (Polychromatic418967fa.accept_21_3_9_10_1_6992 3 72 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 136 2 1 36 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 136
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 136))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 71 136 (Eq.refl
  Bool.true) (allA_of_3_1 66 71 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 70 136 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 70 136 2 33 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 70 136 (accept_3_3 65 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70
  136 2 32 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  70 136 (Polychromatic418967fa.accept_13_11_5_6_1_519 63 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 70 136 2 31 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 70 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 61 70 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 136 2 30 35 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 136 (accept_3_3 59 70 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70 136 2 29 35 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 70 136
  (Polychromatic418967fa.accept_9_3_7_1_1_143 57 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 70 136 2 28 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 70 136 (Polychromatic418967fa.accept_12_7_10_4_1_382 55 70 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 70 136 2 27 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 136 (accept_3_3 53 70 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 136 2 26 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 136 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 70 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 136 2 25 35 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 136
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 70 136 2 24 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 70 136 (accept_3_3 47 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70
  136 2 23 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  70 136 (Polychromatic418967fa.accept_19_7_13_3_1_4171 45 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 70 136 2 22 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 70 136 (Polychromatic418967fa.accept_12_7_10_4_1_382 43 70 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 136 2 21 35 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 136 (accept_3_3 41 70 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 136 2 20 35 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 136
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 70 136 2 19 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 70 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 70 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 136 2 18 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 70 136 (accept_3_3 35 70 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70 136 2 17 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 136 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 70 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 136 2 16 35 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 136
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 70 136 2 15 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 70 136 (accept_3_3 29 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70
  136 2 14 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  70 136 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 70 136 2 13 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 70 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 70 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 136 2 12 35 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 136 (accept_3_3 23 70 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 136 2 11 35 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 136
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 136 2 10 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 136 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 70 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 136 2 9 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 136 (accept_3_3 17 70 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 70 136 2 8 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 70 136 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 70 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 136 2 7 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 136 2 6 35 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 136 (accept_3_3 11
  70 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 136 2 5 35 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 136
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 70 136 2 4 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 70 136 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 70 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 136 2 3 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 136 (accept_3_3 5 70 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 70 136 2 2 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 70 136 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 70 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 136 2 1 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  136))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 69 136 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 69 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 69 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 69 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 136 (accept_3_3 65 69 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 136 (Polychromatic418967fa.accept_19_7_12_3_1_4169
  64 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 136
  (Polychromatic418967fa.accept_10_3_9_6_1_94 63 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 136 (accept_3_3 62 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 136 (accept_3_3 59 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 69 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 136 (accept_3_3 56 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 136 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 136 (accept_3_3 53 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 69 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 136
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 136 (accept_3_3 50 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 136 (accept_3_3 47 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 69 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 136
  (Polychromatic418967fa.accept_10_5_9_6_1_697 45 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 136 (accept_3_3 44 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 136 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 136 (accept_3_3 41 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 136 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 69 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 136
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 136 (accept_3_3 38 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 136 (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 69 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 136 (accept_3_3 35 69 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 69 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 136
  (Polychromatic418967fa.accept_10_3_9_6_1_94 33 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 136 (accept_3_3 32 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 136 (accept_3_3 29 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 136 (Polychromatic418967fa.accept_13_2_4_6_1_2356 28 69 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 136
  (Polychromatic418967fa.accept_16_11_5_8_1_2427 27 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 136 (accept_3_3 26 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 136 (Polychromatic418967fa.accept_13_11_4_6_1_1006 24 69 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 136 (accept_3_3 23 69 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 136 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 69 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 136 (accept_3_3 20 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 136 (accept_3_3 17 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 69 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 136
  (Polychromatic418967fa.accept_10_5_9_6_1_697 15 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 136 (accept_3_3 14 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 136 (accept_3_3 11 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 136 (Polychromatic418967fa.accept_13_10_4_6_1_3224 10 69 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 136
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 136 (accept_3_3 8 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 136 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 136 (accept_3_3 5 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 69
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 136 (accept_3_3 2 69 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  136)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 136 (allA_of_3_1 68 68 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 136 (allA_succ_of_accept 66 67 136
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 136 (accept_3_3 65 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 136 (accept_3_3 62 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 67 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 136
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 136 (accept_3_3 59 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 136 (accept_3_3 56 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 67 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 136
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 136 (accept_3_3 53 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 136 (accept_3_3 50 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 136 (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 67 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 136
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 136 (accept_3_3 47 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 136 (accept_3_3 44 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 67 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 136
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 136 (accept_3_3 41 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 136 (Polychromatic418967fa.accept_13_1_2_6_1_515 40 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 136 (accept_3_3 38 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 136 (Polychromatic418967fa.accept_16_5_3_8_1_4555 37 67 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 136
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 136 (accept_3_3 35 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 136 (accept_3_3 32 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 136 (Polychromatic418967fa.accept_10_1_7_6_1_91 31 67 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 136
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 136 (accept_3_3 29 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 136 (Polychromatic418967fa.accept_16_12_3_8_1_5729 28 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 136 (accept_3_3 26 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 67 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 136
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 136 (accept_3_3 23 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 136 (accept_3_3 20 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 136 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 67 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 136
  (Polychromatic418967fa.accept_24_18_19_16_1_5217 18 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 67 136 (accept_3_3 17 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 67 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 136 (accept_3_3 14 67 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 13
  67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 136
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 136 (accept_3_3 11 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 136 (accept_3_3 8 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 136
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 136 (accept_3_3 5 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  136 (Polychromatic418967fa.accept_13_4_2_6_1_1043 4 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 136 (accept_3_3 2 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 67 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  136))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 136 (allA_succ_of_accept 65 66
  136 (accept_3_3 65 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 136 2 32 33 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 136
  (Polychromatic418967fa.accept_12_3_6_4_1_400 63 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 136 2 31 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 66 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 136 2 30 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 136 (accept_3_3 59 66 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 136 2 29 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 136 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 66 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 136 2 28 33 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 136
  (Polychromatic418967fa.accept_13_3_1_6_1_509 55 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 136 2 27 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 136 (accept_3_3 53 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66
  136 2 26 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  66 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 66 136 2 25 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 66 136 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 66 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 136 2 24 33 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 136 (accept_3_3 47 66 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 136 2 23 33 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 136
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 136 2 22 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 66 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 136 2 21 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 136 (accept_3_3 41 66 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 136 2 20 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 136 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 66 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 136 2 19 33 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 136
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 37 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 136 2 18 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 136 (accept_3_3 35 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66
  136 2 17 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  66 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 66 136 2 16 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 66 136 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 66 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 136 2 15 33 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 136 (accept_3_3 29 66 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 136 2 14 33 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 136
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 136 2 13 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 66 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 136 2 12 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 136 (accept_3_3 23 66 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 136 2 11 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 136 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 66 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 136 2 10 33 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 136
  (Polychromatic418967fa.accept_24_19_18_16_1_5216 19 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 66 136 2 9 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 66 136 (accept_3_3 17 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 66 136 2 8 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 66 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 66 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 136 2 7 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 136 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 66 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 136 2 6 33 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 136 (accept_3_3 11 66 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 136 2 5 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 136 (Polychromatic418967fa.accept_12_9_6_4_1_402 9
  66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 136 2 4 33 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 136
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 136 2 3 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 136 (accept_3_3 5 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 136
  2 2 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66
  136 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 66 136 2 1 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 136 (Polychromatic418967fa.accept_20_1_6_16_1_6991 1 66 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 136))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 136 (allA_of_3_1 65 65 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 136
  (allA_succ_of_accept 63 64 136 (Polychromatic418967fa.accept_15_3_4_1_1_1072 63 64 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 64 136 2 31 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 64 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 61
  64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 136 4 15 16 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 136 (accept_3_3 59
  64 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 136 2 29 32 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 136
  (Polychromatic418967fa.accept_11_2_9_4_1_310 57 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 136 8 7 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 136 (Polychromatic418967fa.accept_10_5_4_6_1_319 55 64 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 136 2 27 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 136 (accept_3_3 53 64 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 136 4 13 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 64 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 136 2 25 32 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 136
  (Polychromatic418967fa.accept_13_10_12_6_1_991 49 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 136 8 6 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 136 (accept_3_3 47 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  136 2 23 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 136 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 136 4 11 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 136 (Polychromatic418967fa.accept_19_5_7_3_1_6990 43 64 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 136 2 21 32 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 136 (accept_3_3 41 64 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 136 8 5 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 136 (Polychromatic418967fa.accept_7_4_1_3_1_277 39
  64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 136 2 19 32 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 136
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 136 4 9 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 136 (accept_3_3 35 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  136 2 17 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  64 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 136 8 4 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 64 136 (Polychromatic418967fa.accept_13_5_12_6_1_508 31 64 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 136 2 15 32 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 136 (accept_3_3 29 64 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 136 4 7 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 136 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 64 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 136 2 13 32 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 136
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 136 8 3 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 64 136 (accept_3_3 23 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64
  136 2 11 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  64 136 (Polychromatic418967fa.accept_22_21_20_4_1_6989 21 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 64 136 4 5 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 64 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 64 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 136 2 9 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 136 (accept_3_3 17 64 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 136 8 2 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 64 136 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 64 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 136 2 7 32 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 136
  (Polychromatic418967fa.accept_11_2_9_4_1_310 13 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 136 4 3 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 136 (accept_3_3 11 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64
  136 2 5 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  64 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 64 136 8 1 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 64 136 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 64 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 136 2 3 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 136 (accept_3_3 5 64 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 136 4 1 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 64 136 (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 64 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 136 2 1 32 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 136
  (Polychromatic418967fa.accept_23_1_18_21_1_6988 1 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 136)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 136
  (allA_succ_of_accept 62 63 136 (accept_3_3 62 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 136 (Polychromatic418967fa.accept_13_8_11_6_1_1035 60 63 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 136 (accept_3_3 59 63 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 136 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 63 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 136
  (Polychromatic418967fa.accept_10_7_3_6_1_644 57 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 136 (accept_3_3 56 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 136 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 136 (accept_3_3 53 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 136 (Polychromatic418967fa.accept_16_4_15_8_1_2413 52 63 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 136
  (Polychromatic418967fa.accept_11_7_8_4_1_718 51 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 136 (accept_3_3 50 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 136 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 136 (accept_3_3 47 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 136 (Polychromatic418967fa.accept_14_4_7_10_1_3888 46 63 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 136
  (Polychromatic418967fa.accept_11_1_8_4_1_717 45 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 136 (accept_3_3 44 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 136 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 136 (accept_3_3 41 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 136 (Polychromatic418967fa.accept_11_7_8_4_1_718 40 63 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 136
  (Polychromatic418967fa.accept_10_9_3_6_1_686 39 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 136 (accept_3_3 38 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 136 (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 136 (accept_3_3 35 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 136 (Polychromatic418967fa.accept_11_1_8_4_1_717 34 63 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 136
  (Polychromatic418967fa.accept_16_1_15_8_1_2411 33 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 136 (accept_3_3 32 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 136 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 136 (accept_3_3 29 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 136 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 63 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 136
  (Polychromatic418967fa.accept_10_7_3_6_1_644 27 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 136 (accept_3_3 26 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 136 (Polychromatic418967fa.accept_19_5_6_3_1_5578 24 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 136 (accept_3_3 23 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 136 (Polychromatic418967fa.accept_23_22_17_21_1_6987 22 63 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 136
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 21 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 136 (accept_3_3 20 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 136 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 136 (accept_3_3 17 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 136 (Polychromatic418967fa.accept_19_16_6_3_1_6972 16 63 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 136
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 15 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 136 (accept_3_3 14 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 136 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 136 (accept_3_3 11 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 136 (Polychromatic418967fa.accept_24_10_15_16_1_6986 10 63 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 136
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 136 (accept_3_3 8 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 136 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 63 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 136 (accept_3_3 5 63 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 136 (Polychromatic418967fa.accept_13_4_11_6_1_1033 4 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 136 (Polychromatic418967fa.accept_14_3_7_10_1_2146
  3 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 136 (accept_3_3 2 63
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  136))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 136 (allA_of_3_1 62 62 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 136 (allA_succ_of_accept 60 61 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 136 (accept_3_3 59 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 136 (accept_3_3 56 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 136 (Polychromatic418967fa.accept_10_5_1_6_1_672 55 61 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 136
  (Polychromatic418967fa.accept_13_2_9_6_1_501 54 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 136 (accept_3_3 53 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 136 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 136 (accept_3_3 50 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 61 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 136
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 136 (accept_3_3 47 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 136 (Polychromatic418967fa.accept_11_2_6_4_1_3028 46 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 136 (accept_3_3 44 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 61 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 136 (accept_3_3 41 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 136 (accept_3_3 38 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 61 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 136
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 136 (accept_3_3 35 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 136 (accept_3_3 32 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 61 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 136
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 136 (accept_3_3 29 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 136 (Polychromatic418967fa.accept_13_2_9_6_1_501 28 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 136 (accept_3_3 26 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 136 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 61 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 136 (accept_3_3 23 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 136 (accept_3_3 20 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 136 (Polychromatic418967fa.accept_16_3_13_8_1_1594 19 61 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 136
  (Polychromatic418967fa.accept_19_18_4_3_1_4140 18 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 136 (accept_3_3 17 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 136 (accept_3_3 14 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 61 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 136
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 136 (accept_3_3 11 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 136 (accept_3_3 8 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 136 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 61 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 136 (accept_3_3 5 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  136 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 136 (accept_3_3 2 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 136)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 136 (allA_succ_of_accept 59 60 136 (accept_3_3 59 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 136 2 29 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 60 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 136 4 14 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 55
  60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 136 2 27 30 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 136 (accept_3_3 53
  60 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 136 4 13 15 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 136
  (Polychromatic418967fa.accept_16_3_12_8_1_808 51 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 136 2 25 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 136 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 60 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 136 4 12 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 136 (accept_3_3 47 60 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 136 2 23 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 136 (Polychromatic418967fa.accept_16_13_12_8_1_2451 45 60
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 136 4 11 15 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 136
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 136 2 21 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 136 (accept_3_3 41 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60
  136 4 10 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  60 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 60 136 2 19 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 60 136 (Polychromatic418967fa.accept_13_11_8_6_1_1023 37 60 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 136 4 9 15 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 136 (accept_3_3 35 60 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 136 2 17 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 136 (Polychromatic418967fa.accept_16_1_12_8_1_2405
  33 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 136 4 8 15 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 136
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 136 2 15 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 136 (accept_3_3 29 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60
  136 4 7 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  60 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 60 136 2 13 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 60 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 60 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 136 4 6 15 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 136 (accept_3_3 23 60 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 136 2 11 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 21
  60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 136 4 5 15 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 136
  (Polychromatic418967fa.accept_16_3_12_8_1_808 19 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 136 2 9 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 136 (accept_3_3 17 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60
  136 4 4 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  60 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 60 136 2 7 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 60 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 136 4 3 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 136 (accept_3_3 11 60 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 136 2 5 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 60 136 (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 60 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 136 4 2 15 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 136
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 136 2 3 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 136 (accept_3_3 5 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 136
  4 1 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60
  136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 136 2 1 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 136))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 136 (allA_of_3_1 59 59 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 136
  (allA_succ_of_accept 57 58 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 58 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 58 136 2 28 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 58 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 55
  58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 136 2 27 29 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 136 (accept_3_3 53
  58 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 136 2 26 29 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 136
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 58 136 2 25 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 58 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 58 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 58 136 2 24 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 58 136 (accept_3_3 47 58 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 136 2 23 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 136 (Polychromatic418967fa.accept_20_5_18_16_1_1558 45 58
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 136 2 22 29 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 136
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 136 2 21 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 58 136 (accept_3_3 41 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58
  136 2 20 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  58 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 58 136 2 19 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 58 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 58 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 136 2 18 29 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 136 (accept_3_3 35 58 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 136 2 17 29 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 136
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 58 136 2 16 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 58 136 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 58 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 136 2 15 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 136 (accept_3_3 29 58 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 136 2 14 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 58 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 136 2 13 29 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 136
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 136 2 12 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 58 136 (accept_3_3 23 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58
  136 2 11 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  58 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 58 136 2 10 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 58 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 58 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 136 2 9 29 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 136 (accept_3_3 17 58 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58 136 2 8 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 58 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 58 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 136 2 7 29 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 136
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 58 136 2 6 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 58 136 (accept_3_3 11 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58
  136 2 5 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  58 136 (Polychromatic418967fa.accept_21_9_16_10_1_5371 9 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 58 136 2 4 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 58 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 58 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 136 2 3 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 136 (accept_3_3 5 58 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 136 2 2 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 58 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 58 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 136 2 1 29 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 136
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 136)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 136 (allA_succ_of_accept 56
  57 136 (accept_3_3 56 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 136
  (Polychromatic418967fa.accept_6_1_3_4_1_1 55 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 136 (accept_3_3 53 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 51
  57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 136 (accept_3_3 50 57
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 136 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 136
  (Polychromatic418967fa.accept_21_6_15_10_1_2579 48 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 136 (accept_3_3 47 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 136 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 136 (Polychromatic418967fa.accept_21_3_15_10_1_3895 45 57 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 136 (accept_3_3 44 57 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 57 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 136
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 136 (accept_3_3 41 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 136 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 136 (accept_3_3 38 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 136
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 136 (accept_3_3 35 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 136 (accept_3_3 32 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 57 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 136
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 136 (accept_3_3 29 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 136 (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 136 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 136 (accept_3_3 26 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 136
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 136 (accept_3_3 23 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 136 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 136 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 136 (accept_3_3 20 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 57 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 136
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 136 (accept_3_3 17 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 136 (accept_3_3 14 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 136
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 136 (accept_3_3 11 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 136 (Polychromatic418967fa.accept_13_10_5_6_1_1671 10 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 136 (accept_3_3 8 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 57 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 136
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 136 (accept_3_3 5 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  136 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 136 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 136 (accept_3_3 2 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 136)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 136 (allA_of_3_1 56 56 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 136
  (allA_succ_of_accept 54 55 136 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 55 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 136 (accept_3_3 53 55 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 136 (Polychromatic418967fa.accept_15_7_10_1_1_1836 52 55 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 136 (accept_3_3 50 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 136 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 136 (Polychromatic418967fa.accept_13_9_3_6_1_1661 48 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 136 (accept_3_3 47 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 55 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 136 (accept_3_3 44 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 136 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 136 (Polychromatic418967fa.accept_23_19_9_21_1_6985 42 55 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 136 (accept_3_3 41 55 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 136 (Polychromatic418967fa.accept_13_1_3_6_1_158 40 55 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 136 (accept_3_3 38 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 136 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 55 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 136 (accept_3_3 35 55 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 136 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 55 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 136 (accept_3_3 32 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 136 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 136 (accept_3_3 29 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 136 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 55 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 136 (accept_3_3 26 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 136 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 136 (accept_3_3 23 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 55 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 136 (accept_3_3 20 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 136 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 136 (accept_3_3 17 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 55 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 136 (accept_3_3 14 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 136 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 136 (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 55 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 136 (accept_3_3 11 55 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 55 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 136 (accept_3_3 8 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  136 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 55 136 (Polychromatic418967fa.accept_15_6_10_1_1_3675 6 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 136 (accept_3_3 5 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 55 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 136 (accept_3_3 2 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55
  136 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 55 136))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 136 (allA_succ_of_accept 53 54
  136 (accept_3_3 53 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 136 2 26 27 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 136
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 54 136 2 25 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 136 (Polychromatic418967fa.accept_11_5_10_4_1_1157 49 54 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 136 2 24 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 136 (accept_3_3 47 54 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 136 2 23 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 136 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 54 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 136 2 22 27 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 136
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 136 2 21 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 136 (accept_3_3 41 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54
  136 2 20 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  54 136 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 54 136 2 19 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 54 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 54 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 136 2 18 27 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 136 (accept_3_3 35 54 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 136 2 17 27 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 136
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 136 2 16 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 136 (Polychromatic418967fa.accept_25_6_4_11_1_6984 31 54 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 136 2 15 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 136 (accept_3_3 29 54 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 136 2 14 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 136 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 54 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 136 2 13 27 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 136
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 136 2 12 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 136 (accept_3_3 23 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54
  136 2 11 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  54 136 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 54 136 2 10 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 54 136 (Polychromatic418967fa.accept_14_5_12_10_1_2985 19 54 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 136 2 9 27 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 136 (accept_3_3 17 54 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 136 2 8 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 54 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 136 2 7 27 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 136
  (Polychromatic418967fa.accept_19_13_16_3_1_6983 13 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 136 2 6 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 136 (accept_3_3 11 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54
  136 2 5 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  54 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 54 136 2 4 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 54 136 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 54 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 136 2 3 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 136 (accept_3_3 5 54 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 136 2 2 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 54 136 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 54 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 136 2 1 27 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 136
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 136)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 136 (allA_of_3_1 53 53 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 136 (allA_succ_of_accept 51 52 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 51 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 136 2 25 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 52 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 136 4 12 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 136 (accept_3_3 47 52 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 136 2 23 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 136 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 52 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 136 4 11 13 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 136
  (Polychromatic418967fa.accept_16_11_4_8_1_3435 43 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 136 2 21 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 136 (accept_3_3 41 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  136 4 10 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 136 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 136 2 19 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 136 (Polychromatic418967fa.accept_16_5_4_8_1_1560 37 52 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 136 4 9 13 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 136 (accept_3_3 35 52 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 136 2 17 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 136 (Polychromatic418967fa.accept_9_6_7_1_1_145 33
  52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 136 4 8 13 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 136
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 136 2 15 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 52 136 (accept_3_3 29 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52
  136 4 7 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  52 136 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 52 136 2 13 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 52 136 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 52 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 136 4 6 13 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 136 (accept_3_3 23 52 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 136 2 11 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 136 (Polychromatic418967fa.accept_9_3_7_1_1_143 21
  52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 136 4 5 13 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 136
  (Polychromatic418967fa.accept_16_3_4_8_1_3450 19 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 136 2 9 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 136 (accept_3_3 17 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  136 4 4 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 136 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 136 2 7 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 52 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 52 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 136 4 3 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 136 (accept_3_3 11 52 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 136 2 5 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 52 136 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 52 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 136 4 2 13 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 136
  (Polychromatic418967fa.accept_11_7_8_4_1_718 7 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 52 136 2 3 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 52 136 (accept_3_3 5 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 136
  4 1 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52
  136 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 136 2 1 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 136 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 52 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 136)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 136
  (allA_succ_of_accept 50 51 136 (accept_3_3 50 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  51 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 136 (accept_3_3 47 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 136 (Polychromatic418967fa.accept_13_7_12_6_1_1039 46 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 136
  (Polychromatic418967fa.accept_10_5_1_6_1_672 45 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 136 (accept_3_3 44 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 136 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 136 (accept_3_3 41 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 136 (accept_3_3 38 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 136 (accept_3_3 35 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 51 136 17 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 51 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 136 (accept_3_3 32 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 136 (accept_3_3 29 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 136 (Polychromatic418967fa.accept_13_2_12_6_1_2394 28 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 136 (accept_3_3 26 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 136
  (Polychromatic418967fa.accept_15_9_6_1_1_493 24 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 136 (accept_3_3 23 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 136 (accept_3_3 20 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 136
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 17 51 136 17 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 16 51 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 136 (accept_3_3 14 51 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13
  51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 136
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 136 (accept_3_3 11 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 136 (Polychromatic418967fa.accept_13_10_12_6_1_991 10 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 136 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 136 (accept_3_3 8 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 136
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 136 (accept_3_3 5 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  136 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 136 (accept_3_3 2 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 136)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 136 (allA_of_3_1 50 50 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 136
  (allA_succ_of_accept 48 49 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 136 (accept_3_3 47 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 49 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 136 (accept_3_3 44 49
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 136
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 136 (accept_3_3 41 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 136 (Polychromatic418967fa.accept_18_4_13_10_1_2064 40 49 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 136 (accept_3_3 38 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 136 (Polychromatic418967fa.accept_18_1_13_10_1_2024 37 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 136 (Polychromatic418967fa.accept_16_4_1_8_1_835 36 49 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 136 (accept_3_3 35 49 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 49 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 136 (accept_3_3 32 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 136 (Polychromatic418967fa.accept_13_5_10_6_1_2361 31 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 49 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 136 (accept_3_3 29 49 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 136 (Polychromatic418967fa.accept_13_2_10_6_1_1676 28 49 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 136 (accept_3_3 26 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 136 (accept_3_3 23 49 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 49 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 136 (accept_3_3 20 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 136 (Polychromatic418967fa.accept_18_1_13_10_1_2024 19 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 136 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 49 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 136 (accept_3_3 17 49 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 136 (accept_3_3 14 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 136 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 49 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 136 (accept_3_3 11 49 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 136 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 49 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 136 (accept_3_3 8 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  136 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 136 (accept_3_3 5 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 136 (Polychromatic418967fa.accept_13_4_10_6_1_989 4 49 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 49
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 136 (accept_3_3 2 49 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 136 (Polychromatic418967fa.accept_18_1_13_10_1_2024
  1 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  136))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 136 (allA_succ_of_accept 47 48 136 (accept_3_3 47
  48 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 136 2 23 24 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 136
  (Polychromatic418967fa.accept_14_3_6_10_1_752 45 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 136 4 11 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 48 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 136 2 21 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 136 (accept_3_3 41 48 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 136 8 5 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 48 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 136 2 19 24 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 136
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 136 4 9 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 136 (accept_3_3 35 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48
  136 2 17 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  48 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 48 136 8 4 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 48 136 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 48 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 136 2 15 24 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 136 (accept_3_3 29 48 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 136 4 7 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 136 (Polychromatic418967fa.accept_13_1_9_6_1_146 27 48 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 136 2 13 24 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 136
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 136 8 3 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 136 (accept_3_3 23 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48
  136 2 11 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  48 136 (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 48 136 4 5 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 136 (Polychromatic418967fa.accept_15_4_3_1_1_487 19 48 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 136 2 9 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 136 (accept_3_3 17 48 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 136 8 2 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 48 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 48 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 136 2 7 24 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 136
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 136 4 3 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 136 (accept_3_3 11 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48
  136 2 5 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  48 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 48 136 8 1 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 48 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 136 2 3 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 136 (accept_3_3 5 48 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 136 4 1 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 48 136 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 48 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 136 2 1 24 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 136
  (Polychromatic418967fa.accept_13_1_9_6_1_146 1 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 136)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 136 (allA_of_3_1 47 47 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 46 136 (allA_succ_of_accept 45 46 136
  (Polychromatic418967fa.accept_24_21_22_16_1_6982 45 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 46 136 2 22 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 46 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 46 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 136 2 21 23 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 136 (accept_3_3 41 46 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 136 2 20 23 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 136
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 46 136 2 19 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 46 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 46 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 136 2 18 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 136 (accept_3_3 35 46 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 136 2 17 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 136 (Polychromatic418967fa.accept_19_14_8_3_1_6981 33 46 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 136 2 16 23 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 136
  (Polychromatic418967fa.accept_11_9_2_4_1_707 31 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 136 2 15 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 46 136 (accept_3_3 29 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46
  136 2 14 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  46 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 46 136 2 13 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 46 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 46 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 136 2 12 23 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 136 (accept_3_3 23 46 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 136 2 11 23 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 136
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 21 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 136 2 10 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 136 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 46 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 136 2 9 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 136 (accept_3_3 17 46 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 136 2 8 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 46 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 136 2 7 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 13
  46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 136 2 6 23 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 136 (accept_3_3 11
  46 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 136 2 5 23 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 136
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 136 2 4 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 136 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 46 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 136 2 3 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 136 (accept_3_3 5 46 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 136 2 2 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 136 (Polychromatic418967fa.accept_27_3_19_1_1_6980 3 46 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 136 2 1 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 46
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  136)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 136 (allA_succ_of_accept 44 45 136 (accept_3_3 44 45
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 136 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 136
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 136 (accept_3_3 41 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  45 136 (Polychromatic418967fa.accept_23_17_22_21_1_6979 40 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 136 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 136 (accept_3_3 38 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 136
  (Polychromatic418967fa.accept_16_4_13_8_1_3424 36 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 136 (accept_3_3 35 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 136 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 136 (Polychromatic418967fa.accept_18_15_9_10_1_1082 33 45 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 136 (accept_3_3 32 45 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 45 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 136
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 136 (accept_3_3 29 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 136 (Polychromatic418967fa.accept_16_12_13_8_1_2409 28 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 136 (Polychromatic418967fa.accept_14_13_3_10_1_2159 27 45 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 136 (accept_3_3 26 45 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 136
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 136 (accept_3_3 23 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 136 (Polychromatic418967fa.accept_21_1_3_10_1_5401 22 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 136 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 136 (accept_3_3 20 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 45 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 136
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 136 (accept_3_3 17 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 136 (Polychromatic418967fa.accept_21_16_3_10_1_6978 16 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 136 (Polychromatic418967fa.accept_18_15_9_10_1_1082 15 45 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 136 (accept_3_3 14 45 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 136
  (Polychromatic418967fa.accept_16_12_13_8_1_2409 12 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 136 (accept_3_3 11 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 136 (Polychromatic418967fa.accept_19_10_7_3_1_6977 10 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 136 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 136 (accept_3_3 8 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 45 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 136
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 136 (accept_3_3 5 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  136 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 136 (Polychromatic418967fa.accept_16_3_13_8_1_1594 3 45 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 136 (accept_3_3 2 45 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 136))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  136 (allA_of_3_1 44 44 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 136 (allA_succ_of_accept 42 43 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 136 (accept_3_3 41 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 136 (accept_3_3 38 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 43 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 136
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 136 (accept_3_3 35 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 136 (accept_3_3 32 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 43 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 136
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 136 (accept_3_3 29 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 136 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 136 (accept_3_3 26 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 136 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 43 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 136 (accept_3_3 23 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 136 (accept_3_3 20 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 136
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 136 (accept_3_3 17 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 136 (accept_3_3 14 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 136 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 43 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 136
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 136 (accept_3_3 11 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 136 (accept_3_3 8 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 136 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 43 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 136 (accept_3_3 5 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  136 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 136 (accept_3_3 2 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 136 (Polychromatic418967fa.accept_19_1_5_3_1_6970 1 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 136))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 136
  (allA_succ_of_accept 41 42 136 (accept_3_3 41 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42
  136 2 20 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  42 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 42 136 2 19 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 42 136 (Polychromatic418967fa.accept_19_18_4_3_1_4140 37 42 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 136 2 18 21 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 136 (accept_3_3 35 42 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 136 2 17 21 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 136
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 136 2 16 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 136 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 42 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 136 2 15 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 136 (accept_3_3 29 42 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 136 2 14 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 136 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 42 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 136 2 13 21 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 136
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 136 2 12 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 136 (accept_3_3 23 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42
  136 2 11 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  42 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 42 136 2 10 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 42 136 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 42 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 136 2 9 21 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 136 (accept_3_3 17 42 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 136 2 8 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 136 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 42 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 136 2 7 21 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 136
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 42 136 2 6 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 42 136 (accept_3_3 11 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42
  136 2 5 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  42 136 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 42 136 2 4 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 42 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 42 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 136 2 3 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 136 (accept_3_3 5 42 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 136 2 2 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 42 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 42 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 136 2 1 21 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 136
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 136)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 136 (allA_of_3_1 41 41 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 40 136 (allA_succ_of_accept 39 40 136
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 136 2 19 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 40 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 136 4 9 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 136 (accept_3_3 35 40 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 40 136 2 17 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 40 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 40 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 136 8 4 5 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 136
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 31 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 136 2 15 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 136 (accept_3_3 29 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  136 4 7 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 136 (Polychromatic418967fa.accept_22_5_18_4_1_327 27 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 136 2 13 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 40 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 136 8 3 5 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 136 (accept_3_3 23 40 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 136 2 11 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 21
  40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 136 4 5 10 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 136
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 40 136 2 9 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 40 136 (accept_3_3 17 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40
  136 8 2 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  40 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 40 136 2 7 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 40 136 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 40 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 136 4 3 10 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 136 (accept_3_3 11 40 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 136 2 5 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 40 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 136 8 1 5 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 136
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 40 136 2 3 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 40 136 (accept_3_3 5 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 136
  4 1 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40
  136 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 40 136 2 1 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 40 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 40 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 40 136)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 136
  (allA_succ_of_accept 38 39 136 (accept_3_3 38 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  39 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 39 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 136 (accept_3_3 35 39 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 39 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 136
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 136 (accept_3_3 32 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 136 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 39 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 136 (accept_3_3 29 39 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 136 (Polychromatic418967fa.accept_16_12_7_8_1_1589 28 39 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 136
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 136 (accept_3_3 26 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 39 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 136 (accept_3_3 23 39 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 39 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 136
  (Polychromatic418967fa.accept_14_7_11_10_1_2155 21 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 136 (accept_3_3 20 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 136 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 39 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 136 (accept_3_3 17 39 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 39 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 136
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 136 (accept_3_3 14 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 136 (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 39 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 136 (accept_3_3 11 39 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 136 (Polychromatic418967fa.accept_15_10_9_1_1_3688 10 39
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 136
  (Polychromatic418967fa.accept_16_9_7_8_1_1588 9 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 136 (accept_3_3 8 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 136 (accept_3_3 5 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 136 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 39 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 136 (Polychromatic418967fa.accept_10_3_9_6_1_94 3
  39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 136 (accept_3_3 2 39 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 39
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  136))))))))))))))))))))))))))))))))))))))) (allB_succ 38 136 (allA_of_3_1 38 38 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 136 (allA_succ_of_accept 36 37 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 136 (accept_3_3 35 37 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 34
  37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 136 (accept_3_3 32 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 136 (Polychromatic418967fa.accept_10_1_7_6_1_91 31 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 136 (Polychromatic418967fa.accept_13_4_11_6_1_1033 30 37 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 136 (accept_3_3 29 37 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 136 (Polychromatic418967fa.accept_16_12_5_8_1_2492 28 37
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 136 (accept_3_3 26 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 136 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 136 (Polychromatic418967fa.accept_15_9_7_1_1_1075 24 37 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 136 (accept_3_3 23 37 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 37 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 136 (accept_3_3 20 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 136 (Polychromatic418967fa.accept_13_5_11_6_1_505 18 37 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 136 (accept_3_3 17 37 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 136 (Polychromatic418967fa.accept_18_16_1_10_1_2029 16 37 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 136 (accept_3_3 14 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 136 (accept_3_3 11 37 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 37 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 136 (accept_3_3 8 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  136 (Polychromatic418967fa.accept_20_7_17_16_1_6976 7 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 37 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 37 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 136 (accept_3_3 5 37 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 136 (Polychromatic418967fa.accept_13_4_11_6_1_1033 4 37 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 136
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 136 (accept_3_3 2 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  136 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 136))))))))))))))))))))))))))))))))))))) (allB_succ 36 136 (allA_succ_of_accept 35 36 136 (accept_3_3 35
  36 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 136 2 17 18 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 136
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 136 4 8 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 136 (Polychromatic418967fa.accept_13_5_10_6_1_2361 31 36 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 136 2 15 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 136 (accept_3_3 29 36 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 136 4 7 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 36 136 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 36 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 136 2 13 18 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 136
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 136 4 6 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 136 (accept_3_3 23 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36
  136 2 11 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  36 136 (Polychromatic418967fa.accept_16_5_4_8_1_1560 21 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 36 136 4 5 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 136 2 9 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 136 (accept_3_3 17 36 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 136 4 4 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 36 136 (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 36 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 136 2 7 18 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 136
  (Polychromatic418967fa.accept_16_13_4_8_1_4557 13 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 136 4 3 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 136 (accept_3_3 11 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36
  136 2 5 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  36 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 36 136 4 2 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 36 136 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 36 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 136 2 3 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 136 (accept_3_3 5 36 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 136 4 1 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 36 136 (Polychromatic418967fa.accept_13_3_10_6_1_2382 3 36 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 136 2 1 18 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 136
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 136)))))))))))))))))))))))))))))))))))) (allB_succ 35 136 (allA_of_3_1 35 35 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 136 (allA_succ_of_accept 33 34 136 (Polychromatic418967fa.accept_9_6_7_1_1_145 33
  34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 136 2 16 17 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 136
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 34 136 2 15 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 34 136 (accept_3_3 29 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34
  136 2 14 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  34 136 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 34 136 2 13 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 34 136 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 34 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 136 2 12 17 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 136 (accept_3_3 23 34 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 136 2 11 17 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 136
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 136 2 10 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 136 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 34 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 136 2 9 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 17 34 136 17 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 16 34 136 2 8 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 136 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 34 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 136 2 7 17 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 136
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 136 2 6 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 136 (accept_3_3 11 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  136 2 5 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 136 2 4 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 136 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 34 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 136 2 3 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 136 (accept_3_3 5 34 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 136 2 2 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 136 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 34 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 136 2 1 17 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 136
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 136)))))))))))))))))))))))))))))))))) (allB_succ 33 136 (allA_succ_of_accept 32 33 136 (accept_3_3 32 33
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 136 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 136
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 136 (accept_3_3 29 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 136 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 136 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 33 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 136 (accept_3_3 26 33 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 136
  (Polychromatic418967fa.accept_18_6_15_10_1_6975 24 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 136 (accept_3_3 23 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 33 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 136 (accept_3_3 20 33 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 33 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 136
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 136 (accept_3_3 17 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 33 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 136 (accept_3_3 14 33 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 136 (accept_3_3 11 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 136 (Polychromatic418967fa.accept_22_10_11_4_1_6974 10 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 136 (accept_3_3 8 33 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 33 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 136
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 136 (accept_3_3 5 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  136 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 33 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 136 (accept_3_3 2 33 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 136))))))))))))))))))))))))))))))))) (allB_succ 32 136
  (allA_of_3_1 32 32 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 136 (allA_succ_of_accept 30 31 136
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 136 (accept_3_3 29 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 136 (Polychromatic418967fa.accept_16_12_15_8_1_4586 28 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 136 (accept_3_3 26 31 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 31 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 136
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 136 (accept_3_3 23 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 136 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 31 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 136 (accept_3_3 20 31 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 136 (Polychromatic418967fa.accept_18_1_13_10_1_2024 19 31 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 136
  (Polychromatic418967fa.accept_20_18_11_16_1_6973 18 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 31 136 (accept_3_3 17 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 31 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 31 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 136 (accept_3_3 14 31 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 136 (Polychromatic418967fa.accept_11_2_9_4_1_310
  13 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 136
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 136 (accept_3_3 11 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 31 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 136 (accept_3_3 8 31 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 136
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 136 (accept_3_3 5 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  136 (Polychromatic418967fa.accept_13_4_5_6_1_3201 4 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 136 (accept_3_3 2 31 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 136 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 31 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 136))))))))))))))))))))))))))))))) (allB_succ 30 136
  (allA_succ_of_accept 29 30 136 (accept_3_3 29 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  136 2 14 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 136 2 13 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 30 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 136 2 12 15 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 136 (accept_3_3 23 30 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 136 2 11 15 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 136
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 136 2 10 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 136 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 30 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 136 2 9 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 136 (accept_3_3 17 30 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 136 2 8 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 30 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 136 2 7 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  30 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 136 2 6 15 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 136 (accept_3_3 11
  30 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 136 2 5 15 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 136
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 136 2 4 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 30 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 136 2 3 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 136 (accept_3_3 5 30 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 136 2 2 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 136 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 30 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 136 2 1 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 30
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 136))))))))))))))))))))))))))))))
  (allB_succ 29 136 (allA_of_3_1 29 29 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 136
  (allA_succ_of_accept 27 28 136 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 28 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 136 2 13 14 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 136 (Polychromatic418967fa.accept_13_12_2_6_1_2396
  25 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 136 4 6 7 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 136 (accept_3_3 23
  28 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 136 2 11 14 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 136
  (Polychromatic418967fa.accept_13_8_2_6_1_2385 21 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 28 136 4 5 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 28 136 (Polychromatic418967fa.accept_16_3_12_8_1_808 19 28 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 136 2 9 14 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 136 (accept_3_3 17 28 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 28 136 4 4 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 28 136 (Polychromatic418967fa.accept_16_15_12_8_1_4585 15 28 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 136 2 7 14 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 136
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 28 136 4 3 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 28 136 (accept_3_3 11 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28
  136 2 5 14 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  28 136 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 28 136 4 2 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 28 136 (Polychromatic418967fa.accept_16_7_12_8_1_2450 7 28 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 136 2 3 14 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 136 (accept_3_3 5 28 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 136 4 1 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 28 136 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 28 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 136 2 1 14 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 136
  (Polychromatic418967fa.accept_13_1_2_6_1_515 1 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 136)))))))))))))))))))))))))))) (allB_succ 27 136 (allA_succ_of_accept 26 27 136 (accept_3_3 26 27 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 25
  27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 136
  (Polychromatic418967fa.accept_19_5_8_3_1_5498 24 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 136 (accept_3_3 23 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  27 136 (Polychromatic418967fa.accept_13_9_1_6_1_510 22 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 136 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 27 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 136 (accept_3_3 20 27 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 136
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 136 (accept_3_3 17 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  27 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 136 (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 27 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 136 (accept_3_3 14 27 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 27 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 136
  (Polychromatic418967fa.accept_16_12_11_8_1_832 12 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 136 (accept_3_3 11 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 136 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 136 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 27 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 136 (accept_3_3 8 27 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 136
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 136 (accept_3_3 5 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  136 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 27 136 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 27 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 136 (accept_3_3 2 27 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 27 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 27 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 136))))))))))))))))))))))))))) (allB_succ 26 136 (allA_of_3_1 26
  26 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 136 (allA_succ_of_accept 24 25 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 136 (accept_3_3 23 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 136 (accept_3_3 20 25 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 136 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 25 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 136
  (Polychromatic418967fa.accept_11_7_3_4_1_729 18 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 136 (accept_3_3 17 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 136 (Polychromatic418967fa.accept_19_16_6_3_1_6972 16 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 25 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 136 (accept_3_3 14 25 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 136
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 136 (accept_3_3 11 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 136 (accept_3_3 8 25 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 136 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 25 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 136
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 136 (accept_3_3 5 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  136 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 25 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 136 (accept_3_3 2 25 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 136))))))))))))))))))))))))) (allB_succ 24 136
  (allA_succ_of_accept 23 24 136 (accept_3_3 23 24 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24
  136 2 11 12 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  24 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 24 136 4 5 6 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 24 136 (Polychromatic418967fa.accept_26_19_24_6_1_6971 19 24 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 136 2 9 12 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 136 (accept_3_3 17 24 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 136 8 2 3 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 136 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 24 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 136 2 7 12 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 136
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 24 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 136 4 3 6 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 136 (accept_3_3 11 24 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  136 2 5 12 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 136 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 24 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 24 136 8 1 3 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 24 136 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 136 2 3 12 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 136 (accept_3_3 5 24 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 136 4 1 6 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 24 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 136 2 1 12 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 136
  (Polychromatic418967fa.accept_19_1_5_3_1_6970 1 24 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 136)))))))))))))))))))))))) (allB_succ 23 136 (allA_of_3_1 23 23 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 136 (allA_succ_of_accept 21 22 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 22 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 136 2 10 11 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 136
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 22 136 2 9 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 22 136 (accept_3_3 17 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22
  136 2 8 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  22 136 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 22 136 2 7 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 22 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 22 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 136 2 6 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 136 (accept_3_3 11 22 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 136 2 5 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 22 136 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 22 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 136 2 4 11 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 136
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 22 136 2 3 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 22 136 (accept_3_3 5 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 136
  2 2 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22
  136 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 22 136 2 1 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 22 136 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 22 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 22 136)))))))))))))))))))))) (allB_succ 21 136 (allA_succ_of_accept 20 21
  136 (accept_3_3 20 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 136
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 136 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 21 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 136 (accept_3_3 17 21 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 21 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 136 (Polychromatic418967fa.accept_9_6_3_1_1_155 15
  21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 136 (accept_3_3 14 21
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 136 (Polychromatic418967fa.accept_6_1_3_4_1_1
  13 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 136
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 136 (accept_3_3 11 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 136 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 136 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 21 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 136 (accept_3_3 8 21 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 21 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 136
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 136 (accept_3_3 5 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  136 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 136 (Polychromatic418967fa.accept_14_3_7_10_1_2146 3 21 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 136 (accept_3_3 2 21 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 136))))))))))))))))))))) (allB_succ 20 136 (allA_of_3_1 20 20
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 136 (allA_succ_of_accept 18 19 136
  (Polychromatic418967fa.accept_11_7_8_4_1_718 18 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 136 (accept_3_3 17 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 136 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 136 (accept_3_3 14 19 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 136 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 19 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 136
  (Polychromatic418967fa.accept_11_1_8_4_1_717 12 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 136 (accept_3_3 11 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 136 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 19 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 136 (accept_3_3 8 19 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 136 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 19 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 136
  (Polychromatic418967fa.accept_25_6_19_11_1_6969 6 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 136 (accept_3_3 5 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  136 (Polychromatic418967fa.accept_16_4_3_8_1_2486 4 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 19 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 136 (accept_3_3 2 19 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 19 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 136))))))))))))))))))) (allB_succ 18 136
  (allA_succ_of_accept 17 18 136 (accept_3_3 17 18 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18
  136 2 8 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  18 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 18 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 18 136 2 7 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 136 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 18 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 136 2 6 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 136 (accept_3_3 11 18 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 136 2 5 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 18 136 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 18 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 136 2 4 9 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 136
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 7 18 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 136 2 3 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 136 (accept_3_3 5 18 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 136
  2 2 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 136
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 18 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 136 2 1 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 136 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 18 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 136)))))))))))))))))) (allB_succ 17 136 (allA_of_3_1 17 17 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 136 (allA_succ_of_accept 15 16 136
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 16 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 136 2 7 8 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 16 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 136 4 3 4 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 136 (accept_3_3 11 16 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 136 2 5 8 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 136 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 16 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 136 8 1 2 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 136 (Polychromatic418967fa.accept_21_7_16_10_1_1349
  7 16 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 136 2 3 8 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 136 (accept_3_3 5 16
  136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 136 4 1 4 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 136
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 16 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 136 2 1 8 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 136 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 16 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 136)))))))))))))))) (allB_succ 15 136 (allA_succ_of_accept 14 15 136
  (accept_3_3 14 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 136
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 136 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 136 (accept_3_3 11 15 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 136 (Polychromatic418967fa.accept_13_10_2_6_1_1044 10 15 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 136
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 136 (accept_3_3 8 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  136 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 15 136 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 15 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 136 (accept_3_3 5 15 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 15 136 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 15 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 136 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 15
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 136 (accept_3_3 2 15 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 15
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 136))))))))))))))) (allB_succ 14 136
  (allA_of_3_1 14 14 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 136 (allA_succ_of_accept 12 13 136
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 136 (accept_3_3 11 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 136 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 136 (accept_3_3 8 13 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 136 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 13 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 136
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 136 (accept_3_3 5 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  136 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 13 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 136 (accept_3_3 2 13 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 136 (Polychromatic418967fa.accept_18_1_13_10_1_2024 1 13 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 136))))))))))))) (allB_succ 12 136 (allA_succ_of_accept 11 12
  136 (accept_3_3 11 12 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 136 2 5 6 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 136
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 136 4 2 3 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 136 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 136 2 3 6 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 136 (accept_3_3 5 12 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 136 4 1 3 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 136 (Polychromatic418967fa.accept_16_3_12_8_1_808 3 12 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 136 2 1 6 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 136 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 136)))))))))))) (allB_succ 11 136
  (allA_of_3_1 11 11 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 136 (allA_succ_of_accept 9 10 136
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 10 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 136 2 4 5 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 136 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 10 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 136 2 3 5 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 136 (accept_3_3 5 10 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 136 2 2 5 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 136 (Polychromatic418967fa.accept_13_3_10_6_1_2382 3 10 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 136 2 1 5 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 136 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  10 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 136)))))))))) (allB_succ 9 136
  (allA_succ_of_accept 8 9 136 (accept_3_3 8 9 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 136
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 9 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 136 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 9 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 136 (accept_3_3 5 9 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 136 (Polychromatic418967fa.accept_13_4_9_6_1_2376 4 9 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 136 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 9
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 136 (accept_3_3 2 9 136
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 136))))))))) (allB_succ 8 136
  (allA_of_3_1 8 8 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 136 (allA_succ_of_accept 6 7 136
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 7 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 136 (accept_3_3 5 7 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 136
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 136 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 136 (accept_3_3 2 7 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 136 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 7 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 136))))))) (allB_succ 6 136 (allA_succ_of_accept 5 6 136
  (accept_3_3 5 6 136 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 136 2 2 3 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 136
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 6 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 136 2 1 3 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 136 (Polychromatic418967fa.accept_19_1_6_3_1_6968 1 6 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 136)))))) (allB_succ 5 136 (allA_of_3_1 5 5 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 136 (allA_succ_of_accept 3 4 136 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 4 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 136 2 1 2 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 136
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 4 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 136)))) (allB_succ 3 136 (allA_succ_of_accept 2 3 136 (accept_3_3 2 3 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 136 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 136))) (allB_succ 2 136 (allA_of_3_1 2 2 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  136))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


