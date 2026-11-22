-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch276_Segment002
-- name    : Polychromatic418967fa_Branch276_Segment002
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:57:20.966977+00:00
-- url     : https://prove2.me/theorems/1ffbb6ac-2a36-439f-85d8-0854bafdb20f
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch276_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_276_segment_002 : allB 185 276 :=
  allB_succ' 93 184 276 (Eq.refl Bool.true) (allA_succ_of_gcd 92 184 276 92 1 2 3 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 184 276
  (Polychromatic418967fa.accept_9_1_4_6_1_5 91 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 184 276 2 45 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 184 276 (accept_3_5 89 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 184 276 4 22 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 184 276 (Polychromatic418967fa.accept_13_9_2_3_1_3027 87 184 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 184 276 2 43 92 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 184 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 85 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 184 276 4 21 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 184 276 (accept_3_5 83 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 184 276 2 41 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 184 276 (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 184 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 184 276 4 20 46 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 184 276
  (Polychromatic418967fa.accept_9_7_4_6_1_273 79 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 184 276 2 39 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 184 276 (accept_3_5 77 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 184 276 4 19 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 184 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 184 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 184 276 2 37 92 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 184 276
  (Polychromatic418967fa.accept_9_1_4_6_1_5 73 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 184 276 4 18 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 184 276 (accept_3_5 71 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 184 276 2 35 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 184 276 23 3 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 68 184 276 4 17 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 184 276 (Polychromatic418967fa.accept_16_3_8_4_1_3279 67 184 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 184 276 2 33 92 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 184 276 (accept_3_5 65 184 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 184 276 4 16 46 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 184 276
  (Polychromatic418967fa.accept_13_11_2_3_1_883 63 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 184 276 2 31 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 184 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 184 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 184 276 4 15 46 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 184 276 (accept_3_5 59 184 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 184 276 2 29 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 184 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 57
  184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 184 276 4 14 46 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 184 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 184 276 2 27 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 184 276 (accept_3_5 53 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 184 276 4 13 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 184 276 (Polychromatic418967fa.accept_13_12_2_3_1_1527 51 184 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 184 276 2 25 92 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 184 276
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 184 276 4 12 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 184 276 (accept_3_5 47 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 184 276 46 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 184 276 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 184 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 184 276 4 11 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 184 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 43
  184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 184 276 2 21 92 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 184 276 (accept_3_5 41
  184 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 184 276 4 10 46 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 184 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 184 276 2 19 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 184 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 184 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 184 276 4 9 46 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 184 276 (accept_3_5 35 184 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 184 276 2 17 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 184 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 33
  184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 184 276 4 8 46 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 184 276
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 31 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 184 276 2 15 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 184 276 (accept_3_5 29 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 184 276 4 7 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 184 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 184 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 276 2 13 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 25
  184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 184 276 4 6 46 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 23 184 276 23 1 8 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 22 184 276 2 11 92 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 184 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 184 276 4 5 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 184 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 184 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 184 276 2 9 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 184 276 (accept_3_5 17 184 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 184 276 4 4 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 184 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 184 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 276 2 7 92 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 184 276 4 3 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 184 276 (accept_3_5 11 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  184 276 2 5 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 184 276 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 184 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 276 4 2 46 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 184 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 184 276 2 3 92 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 184 276 (accept_3_5 5
  184 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184 276 4 1 46 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 184 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 184 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 184 276 2 1 92 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 184 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 184 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 184
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 183
  276 (Eq.refl Bool.true) (allA_succ_of_gcd 93 183 276 3 31 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 183 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 92 183 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 183 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 91 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 183 276 3 30 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 183 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 89 183 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 183 276 (Polychromatic418967fa.accept_7_4_1_3_1_277
  88 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 183 276 3 29 61 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 183 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 86 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 183 276 (Polychromatic418967fa.accept_9_4_3_6_1_532 85 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 183 276 3 28 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 183 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 83
  183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 183 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 82 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 183 276 3 27 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 183 276 (Polychromatic418967fa.accept_9_8_3_6_1_533 80 183 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 183 276 (Polychromatic418967fa.accept_7_2_1_3_1_102
  79 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 183 276 3 26 61 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 183 276
  (Polychromatic418967fa.accept_9_5_3_6_1_269 77 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 183 276 (Polychromatic418967fa.accept_9_4_3_6_1_532 76 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 183 276 3 25 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 183 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 74
  183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 183 276
  (Polychromatic418967fa.accept_9_1_3_6_1_70 73 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 183 276 3 24 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 183 276 (Polychromatic418967fa.accept_9_8_3_6_1_533 71 183 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 183 276 (Polychromatic418967fa.accept_9_7_3_6_1_270
  70 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 183 276 3 23 61 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 183 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 183 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 183 276 3 22 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 183 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 65
  183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 183 276
  (Polychromatic418967fa.accept_9_1_3_6_1_70 64 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 183 276 3 21 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 183 276 (Polychromatic418967fa.accept_9_8_3_6_1_533 62 183 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 183 276 (Polychromatic418967fa.accept_7_5_1_3_1_103
  61 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 183 276 3 20 61 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 183 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 183 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 183 276 3 19 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 183 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 56
  183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 183 276
  (Polychromatic418967fa.accept_9_1_3_6_1_70 55 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 183 276 3 18 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 183 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 183 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 276 (Polychromatic418967fa.accept_9_7_3_6_1_270
  52 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 183 276 3 17 61 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 183 276
  (Polychromatic418967fa.accept_9_5_3_6_1_269 50 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 183 276 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 183 276 3 16 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 183 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 47
  183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 46 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 183 276 3 15 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 183 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 183 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 43
  183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 183 276 3 14 61 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 183 276
  (Polychromatic418967fa.accept_9_5_3_6_1_269 41 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 183 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 183 276 3 13 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 183 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 38
  183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 183 276 3 12 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 183 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 183 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 276 (Polychromatic418967fa.accept_9_7_3_6_1_270
  34 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 183 276 3 11 61 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 183 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 183 276 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 183 276 3 10 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 183 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 276
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 183 276 3 9 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 183 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 183 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 183 276 3 8 61 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 183 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 276 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 183 276 3 7 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 183 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 183 276 3 6 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 183 276 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 183 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 183 276 3 5 61 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 183 276
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 276 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 276 3 4 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 11
  183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 276
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 183 276 3 3 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 183 276 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 183 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 183 276 3 2 61 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 183 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 183 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 276 3 1 61 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 183 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 276
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 183 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 183 276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 95 182 276 (Eq.refl Bool.true) (allA_succ_of_gcd 94 182 276 2 47 91 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 182 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 93 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 182 276 2 46 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 182 276 (accept_3_4 91 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 182 276 2 45 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 182 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 89 182 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 182 276 2 44 91 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 182 276
  (Polychromatic418967fa.accept_15_12_2_6_1_2127 87 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 182 276 2 43 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 182 276 (accept_3_4 85 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 182 276 2 42 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 182 276 (Polychromatic418967fa.accept_15_8_2_6_1_2125 83 182 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 182 276 2 41 91 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 182 276
  (Polychromatic418967fa.accept_10_1_2_6_1_638 81 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 182 276 2 40 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 182 276 (accept_3_4 79 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 182 276 2 39 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 182 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 77 182 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 182 276 2 38 91 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 182 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 75 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 182 276 2 37 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 182 276 (accept_3_4 73 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 182 276 2 36 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 182 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 71 182 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 182 276 2 35 91 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 182 276
  (Polychromatic418967fa.accept_16_5_6_4_1_3211 69 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 182 276 2 34 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 182 276 (accept_3_4 67 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 182 276 2 33 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 182 276 (Polychromatic418967fa.accept_19_8_11_10_1_14236 65 182 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 182 276 2 32 91 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 182 276
  (Polychromatic418967fa.accept_18_9_2_6_1_9322 63 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 182 276 2 31 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 182 276 (accept_3_4 61 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 182 276 2 30 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 182 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 182 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 182 276 2 29 91 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 182 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 57 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 182 276 2 28 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 182 276 (accept_3_4 55 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 182 276 2 27 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 182 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 182 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 182 276 2 26 91 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 182 276
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 182 276 2 25 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 182 276 (accept_3_4 49 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 182 276 2 24 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 182 276 (Polychromatic418967fa.accept_25_22_7_1_1_16967 47 182 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 182 276 2 23 91 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 276
  (Polychromatic418967fa.accept_16_13_6_4_1_3277 45 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 182 276 2 22 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 182 276 (accept_3_4 43 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 182 276 2 21 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 182 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 182 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 276 2 20 91 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 182 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 182 276 2 19 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 182 276 (accept_3_4 37 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 182 276 2 18 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 182 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 182 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 182 276 2 17 91 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 182 276
  (Polychromatic418967fa.accept_21_12_14_3_1_12574 33 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 182 276 2 16 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 182 276 (accept_3_4 31 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 182 276 2 15 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 182 276 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 182 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 276 2 14 91 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 276
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 276 2 13 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 182 276 (accept_3_4 25 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 182 276 2 12 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 182 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 182 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 276 2 11 91 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 182 276 2 10 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 182 276 (accept_3_4 19 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 276 2 9 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 182 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 276 2 8 91 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 276
  (Polychromatic418967fa.accept_19_15_11_10_1_2206 15 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 182 276 2 7 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 182 276 (accept_3_4 13 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 276 2 6 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 276 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 182 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 276 2 5 91 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 276
  (Polychromatic418967fa.accept_17_9_12_4_1_3468 9 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 276 2 4 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 276 (accept_3_4 7 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  276 2 3 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 182 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 276 2 2 91 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 182 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 276 2 1 91 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 276 (accept_3_4 1 182 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 181
  276 (Eq.refl Bool.true) (allA_succ_of_accept 95 181 276 (accept_3_5 95 181 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 181 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 94 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 181 276 (Polychromatic418967fa.accept_7_2_6_3_1_100
  93 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 181 276 (accept_3_5 92
  181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 181 276
  (Polychromatic418967fa.accept_17_6_11_4_1_1525 91 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 181 276 (Polychromatic418967fa.accept_21_6_13_3_1_4851 90 181 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 181 276 (accept_3_5 89 181 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 181 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 181 276 (Polychromatic418967fa.accept_10_7_1_6_1_673
  87 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 181 276 (accept_3_5 86
  181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 181 276
  (Polychromatic418967fa.accept_9_4_1_6_1_284 85 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 181 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 84 181 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 181 276 (accept_3_5 83 181 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 181 276 (Polychromatic418967fa.accept_10_2_1_6_1_634 82 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 181 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 81 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 181 276 (accept_3_5 80 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 181 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 181 276 (Polychromatic418967fa.accept_15_3_1_6_1_206 78 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 181 276 (accept_3_5 77 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 181 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 181 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 181 276
  (Polychromatic418967fa.accept_9_3_1_6_1_86 75 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 181 276 (accept_3_5 74 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 181 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 73 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 181 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 181 276 (accept_3_5 71 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 181 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 181 276
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 69 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 181 276 (accept_3_5 68 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 181 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 181 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 66 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 181 276 (accept_3_5 65 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 181 276 (Polychromatic418967fa.accept_24_16_13_12_1_8475 64 181 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 181 276
  (Polychromatic418967fa.accept_15_3_1_6_1_206 63 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 181 276 (accept_3_5 62 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 181 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 181 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 181 276 (accept_3_5 59 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 181 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 181 276
  (Polychromatic418967fa.accept_8_1_5_4_1_388 57 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 181 276 (accept_3_5 56 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 181 276 (Polychromatic418967fa.accept_10_5_1_6_1_672 55 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 181 276 (Polychromatic418967fa.accept_13_2_12_3_1_415 54 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 181 276 (accept_3_5 53 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 181 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 181 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 181 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 181 276 (accept_3_5 50 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 181 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 181 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 276 (accept_3_5 47 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 181 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 181 276
  (Polychromatic418967fa.accept_10_5_1_6_1_672 45 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 181 276 (accept_3_5 44 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 181 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 181 276 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 276 (accept_3_5 41 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 181 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 181 276 (accept_3_5 38 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 181 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 181 276 (Polychromatic418967fa.accept_27_9_19_6_1_16966 36 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 276 (accept_3_5 35 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 181 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 276
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 276 (accept_3_5 32 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 276 (accept_3_5 29 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 276 (Polychromatic418967fa.accept_11_6_5_1_1_586 28 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 276
  (Polychromatic418967fa.accept_10_7_1_6_1_673 27 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 276 (accept_3_5 26 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 276 (Polychromatic418967fa.accept_15_9_1_6_1_657 24 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 276 (accept_3_5 23 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 181 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 276
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 276 (accept_3_5 20 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 276 (Polychromatic418967fa.accept_22_19_5_12_1_16965 19 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 181 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 276 (accept_3_5 17 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 181 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 276
  (Polychromatic418967fa.accept_10_5_1_6_1_672 15 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 276 (accept_3_5 14 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 276 (accept_3_5 11 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 276 (Polychromatic418967fa.accept_15_10_1_6_1_3033 10 181 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 276 (accept_3_5 8 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 276 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 276 (accept_3_5 5 181 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 181 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 276
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 276 (accept_3_5 2 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 181 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 180
  276 (Eq.refl Bool.true) (allA_succ_of_gcd 96 180 276 12 8 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 180 276 (Polychromatic418967fa.accept_21_11_12_3_1_6461 95 180
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 180 276 2 47 90 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 180 276 3 31 60 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 180 276 4 23 45
  69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 180 276
  (Polychromatic418967fa.accept_17_6_10_4_1_6007 91 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 180 276 6 15 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 180 276 (Polychromatic418967fa.accept_14_5_12_10_1_2985 89 180 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 180 276 4 22 45 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 180 276 3 29 60 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 180 276 2 43 90 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 180 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 85 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 180 276 12 7 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 180 276 (Polychromatic418967fa.accept_13_5_11_3_1_902 83 180 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 180 276 2 41 90 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 180 276 3 27 60 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 180 276 4 20 45 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 180 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 79 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 180 276 6 13 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 180 276 (Polychromatic418967fa.accept_19_1_9_10_1_10391 77 180 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 180 276 4 19 45 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 180 276 3 25 60 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 180 276 2 37 90 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 180 276
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 73 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 180 276 12 6 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 180 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 180 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 180 276 2 35 90 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 180 276 3 23 60 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 180 276 4 17 45 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 180 276
  (Polychromatic418967fa.accept_13_2_11_3_1_873 67 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 180 276 6 11 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 180 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 180 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 180 276 4 16 45 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 180 276 3 21 60 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 180 276 2 31 90 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 180 276
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 61 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 180 276 12 5 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 180 276 (Polychromatic418967fa.accept_13_7_11_3_1_1540 59 180 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 180 276 2 29 90 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 180 276 3 19 60 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 180 276 4 14 45 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 180 276
  (Polychromatic418967fa.accept_21_13_12_3_1_8028 55 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 180 276 6 9 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 180 276 (Polychromatic418967fa.accept_13_1_11_3_1_901 53 180 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 180 276 4 13 45 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 180 276 3 17 60 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 180 276 2 25 90 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 180 276
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 49 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 180 276 12 4 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 180 276 (Polychromatic418967fa.accept_13_8_11_3_1_3053 47 180 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 276 2 23 90 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 180 276 3 15 60 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 180 276 4 11 45 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 276 6 7 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 180 276 (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 180 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 276 4 10 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 180 276 3 13 60 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 180 276 2 19 90 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 276 12 3 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 180 276 (Polychromatic418967fa.accept_19_16_9_10_1_7433 35 180 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 276 2 17 90 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 180 276 3 11 60 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 180 276 4 8 45 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 276
  (Polychromatic418967fa.accept_13_5_11_3_1_902 31 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 276 6 5 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 180 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 180 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 276 4 7 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 180 276 3 9 60 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 180 276 2 13 90 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 276
  (Polychromatic418967fa.accept_19_6_9_10_1_15672 25 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 180 276 12 2 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 180 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 180 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 276 2 11 90 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 180 276 3 7 60 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 180 276 4 5 45 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 276
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 276 6 3 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 180 276 (Polychromatic418967fa.accept_21_17_12_3_1_4848 17 180 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 276 4 4 45 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 276 3 5 60 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 276 2 7 90 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 276
  (Polychromatic418967fa.accept_19_13_9_10_1_2181 13 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 180 276 12 1 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 180 276 (Polychromatic418967fa.accept_17_11_10_4_1_5955 11 180 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 276 2 5 90 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 180 276 3 3 60 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 180 276 4 2 45 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 276
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 180 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 276 6 1 30 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 276 (Polychromatic418967fa.accept_13_5_11_3_1_902 5 180 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 276 4 1 45 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 180 276 3 1 60 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 180 276 2 1 90 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 180 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  179 276 (Eq.refl Bool.true) (allA_succ_of_accept 97 179 276 (accept_3_4 97 179 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 179 276 (Polychromatic418967fa.accept_21_12_11_3_1_1052 96 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 179 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 95 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 179 276 (accept_3_4 94 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 179 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 93 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 179 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 92 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 179 276 (accept_3_4 91 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 179 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 179 276
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 89 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 179 276 (accept_3_4 88 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 179 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 179 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 179 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 86 179 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 179 276 (accept_3_4 85 179 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 179 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 84
  179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 179 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 83 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 179 276 (accept_3_4 82 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 179 276 (Polychromatic418967fa.accept_16_1_3_4_1_665 81 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 179 276 (Polychromatic418967fa.accept_13_2_10_3_1_1538 80 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 179 276 (accept_3_4 79 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 179 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 179 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 179 276
  (Polychromatic418967fa.accept_9_5_8_6_1_281 77 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 179 276 (accept_3_4 76 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 179 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 179 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 74 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 179 276 (accept_3_4 73 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 179 276 (Polychromatic418967fa.accept_13_7_10_3_1_1505 72 179 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 179 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 179 276 (accept_3_4 70 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 179 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 179 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 68 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 179 276 (accept_3_4 67 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 179 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 179 276
  (Polychromatic418967fa.accept_9_2_8_6_1_79 65 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 179 276 (accept_3_4 64 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 179 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 179 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 62 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 179 276 (accept_3_4 61 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 179 276 (Polychromatic418967fa.accept_16_12_3_4_1_4317 60 179 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 179 276
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 179 276 (accept_3_4 58 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 179 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 179 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 56 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 179 276 (accept_3_4 55 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 179 276 (Polychromatic418967fa.accept_13_2_10_3_1_1538 54 179 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 179 276
  (Polychromatic418967fa.accept_10_3_9_6_1_94 53 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 179 276 (accept_3_4 52 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 179 276 (Polychromatic418967fa.accept_18_15_17_6_1_4043 51 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 179 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 179 276 (accept_3_4 49 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 179 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 179 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 179 276 (accept_3_4 46 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 179 276 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 179 276 (Polychromatic418967fa.accept_16_12_3_4_1_4317 44 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 179 276 (accept_3_4 43 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 179 276 (Polychromatic418967fa.accept_19_4_8_10_1_11682 42 179
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 179 276 (accept_3_4 40 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 179 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 179 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 276 (accept_3_4 37 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 179 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 276
  (Polychromatic418967fa.accept_10_5_9_6_1_697 35 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 179 276 (accept_3_4 34 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 179 276 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 179 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 276 (accept_3_4 31 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 179 276 (accept_3_4 28 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 179 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 179 276 (Polychromatic418967fa.accept_31_26_24_28_1_16964 26 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 276 (accept_3_4 25 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 276 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 179
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 179 276 (accept_3_4 22 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 179 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 179 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 276 (accept_3_4 19 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 276 (Polychromatic418967fa.accept_19_18_8_10_1_7489 18 179 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 276
  (Polychromatic418967fa.accept_16_1_3_4_1_665 17 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 276 (accept_3_4 16 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 276 (accept_3_4 13 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 276
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 276 (accept_3_4 10 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 276 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 276 (accept_3_4 7 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 179 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 276
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 276 (accept_3_4 4 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 179 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 276 (accept_3_4 1 179 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  178 276 (Eq.refl Bool.true) (allA_succ_of_gcd 98 178 276 2 49 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 178 276 (Polychromatic418967fa.accept_13_6_9_3_1_915 97 178 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 178 276 2 48 89 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 178 276 (accept_3_5 95
  178 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 178 276 2 47 89 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 178 276
  (Polychromatic418967fa.accept_9_3_7_6_1_76 93 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 178 276 2 46 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 178 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 91 178 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 178 276 2 45 89 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 178 276 (accept_3_5 89 178 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 178 276 2 44 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 178 276 (Polychromatic418967fa.accept_11_10_2_1_1_1036
  87 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 178 276 2 43 89 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 178 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 85 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 178 276 2 42 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 178 276 (accept_3_5 83 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 178 276 2 41 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 178 276 (Polychromatic418967fa.accept_17_13_8_4_1_2514 81 178 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 178 276 2 40 89 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 178 276
  (Polychromatic418967fa.accept_15_4_13_6_1_642 79 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 178 276 2 39 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 178 276 (accept_3_5 77 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 178 276 2 38 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 178 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 75 178 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 178 276 2 37 89 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 178 276
  (Polychromatic418967fa.accept_9_1_7_6_1_75 73 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 178 276 2 36 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 178 276 (accept_3_5 71 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 178 276 2 35 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 178 276 (Polychromatic418967fa.accept_11_3_2_1_1_994 69 178 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 178 276 2 34 89 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 178 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 67 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 178 276 2 33 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 178 276 (accept_3_5 65 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 178 276 2 32 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 178 276 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 178 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 178 276 2 31 89 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 178 276
  (Polychromatic418967fa.accept_20_1_18_16_1_12711 61 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 178 276 2 30 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 178 276 (accept_3_5 59 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 178 276 2 29 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 178 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 178 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 178 276 2 28 89 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 178 276
  (Polychromatic418967fa.accept_9_1_7_6_1_75 55 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 178 276 2 27 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 178 276 (accept_3_5 53 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 178 276 2 26 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 178 276 (Polychromatic418967fa.accept_13_12_9_3_1_3047 51 178 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 178 276 2 25 89 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 178 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 178 276 2 24 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 178 276 (accept_3_5 47 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 178 276 2 23 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 178 276 (Polychromatic418967fa.accept_13_6_9_3_1_915 45 178 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 178 276 2 22 89 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 178 276
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 178 276 2 21 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 178 276 (accept_3_5 41 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 178 276 2 20 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 178 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 178 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 178 276 2 19 89 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 178 276
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 178 276 2 18 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 178 276 (accept_3_5 35 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 178 276 2 17 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 178 276 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 178 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 276 2 16 89 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 276 2 15 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 276 (accept_3_5 29 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 276 2 14 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 276 (Polychromatic418967fa.accept_22_5_2_12_1_10800 27 178 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 276 2 13 89 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 276
  (Polychromatic418967fa.accept_11_3_2_1_1_994 25 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 178 276 2 12 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 178 276 (accept_3_5 23 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 276 2 11 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 178 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 276 2 10 89 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 276
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 276 2 9 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 276 (accept_3_5 17 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 276 2 8 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 276 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 178 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 276 2 7 89 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 276 2 6 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 276 (accept_3_5 11 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 276 2 5 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 276 (Polychromatic418967fa.accept_19_9_7_10_1_1170 9 178 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 276 2 4 89 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 276
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 276 2 3 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 276 (accept_3_5 5 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  276 2 2 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 178 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 276 2 1 89 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 178 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  177 276 (Eq.refl Bool.true) (allA_succ_of_gcd 99 177 276 3 33 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 177 276 (Polychromatic418967fa.accept_13_7_8_3_1_1533 98 177
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 177 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 97 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 177 276 3 32 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 177 276 (Polychromatic418967fa.accept_15_5_12_6_1_639 95 177 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 177 276
  (Polychromatic418967fa.accept_16_14_1_4_1_5432 94 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 177 276 3 31 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 177 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 92 177 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 177 276 (Polychromatic418967fa.accept_10_1_7_6_1_91
  91 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 177 276 3 30 59 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 177 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 89 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 177 276 (Polychromatic418967fa.accept_16_8_1_4_1_6622 88 177 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 177 276 3 29 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 177 276
  (Polychromatic418967fa.accept_20_6_17_16_1_8470 86 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 177 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 177 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 177 276 3 28 59 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 177 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 83 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 177 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 177 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 177 276 3 27 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 177 276 (Polychromatic418967fa.accept_15_5_12_6_1_639
  80 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 177 276
  (Polychromatic418967fa.accept_20_19_17_16_1_2732 79 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 177 276 3 26 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 177 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 77 177 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 177 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 76 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 177 276 3 25 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 177 276 (Polychromatic418967fa.accept_13_9_8_3_1_3045 74 177 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 177 276
  (Polychromatic418967fa.accept_10_3_7_6_1_659 73 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 177 276 3 24 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 177 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 177 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 177 276 (Polychromatic418967fa.accept_13_5_8_3_1_1535
  70 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 177 276 3 23 59 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 177 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 177 276 (Polychromatic418967fa.accept_15_7_12_6_1_1327 67 177 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 177 276 3 22 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 177 276 (Polychromatic418967fa.accept_15_5_12_6_1_639
  65 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 64 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 177 276 3 21 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 177 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 177 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 177 276 (Polychromatic418967fa.accept_7_5_2_3_1_106
  61 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 177 276 3 20 59 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 177 276
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 59 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 177 276 (Polychromatic418967fa.accept_18_4_15_6_1_3994 58 177 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 177 276 3 19 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 177 276 (Polychromatic418967fa.accept_16_8_1_4_1_6622
  56 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 177 276 3 18 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 177 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 177 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 276
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 52 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 177 276 3 17 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 177 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 177 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 276 (Polychromatic418967fa.accept_21_7_9_3_1_8059
  49 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 177 276 3 16 59 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 177 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 177 276 (Polychromatic418967fa.accept_13_7_8_3_1_1533 46 177 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 177 276 3 15 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 177 276 (Polychromatic418967fa.accept_13_5_8_3_1_1535
  44 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 177 276 3 14 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 177 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 177 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 276 (Polychromatic418967fa.accept_7_5_2_3_1_106
  40 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 177 276 3 13 59 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 177 276
  (Polychromatic418967fa.accept_21_17_9_3_1_6437 38 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 177 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 177 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 177 276 3 12 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 177 276 (Polychromatic418967fa.accept_13_9_8_3_1_3045
  35 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 34 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 177 276 3 11 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 177 276 (Polychromatic418967fa.accept_15_2_12_6_1_3063 32 177 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 276
  (Polychromatic418967fa.accept_10_1_7_6_1_91 31 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 177 276 3 10 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 177 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 177 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 276
  (Polychromatic418967fa.accept_16_12_1_4_1_5403 28 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 177 276 3 9 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 177 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 177 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 276 (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 177
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 276 3 8 59 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 276
  (Polychromatic418967fa.accept_10_3_7_6_1_659 23 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 177 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 177 276 3 7 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 177 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 20
  177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 177 276 3 6 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 177 276 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 177 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 276 (Polychromatic418967fa.accept_18_16_15_6_1_4039 16 177
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 276 3 5 59 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 276
  (Polychromatic418967fa.accept_16_14_1_4_1_5432 14 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 177 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 276 3 4 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 276 (Polychromatic418967fa.accept_10_1_7_6_1_91 11
  177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 276
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 10 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 177 276 3 3 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 177 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 177 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 276 (Polychromatic418967fa.accept_13_7_8_3_1_1533
  7 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 276 3 2 59 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 276 (Polychromatic418967fa.accept_18_4_15_6_1_3994 4 177 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 276 3 1 59 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 276 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 177 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 177 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 177 276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 101 176 276 (Eq.refl Bool.true) (allA_succ_of_gcd 100 176 276 4 25 44 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 176 276
  (Polychromatic418967fa.accept_13_8_7_3_1_430 99 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 176 276 2 49 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 176 276 (accept_3_4 97 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 176 276 4 24 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 176 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 95 176 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 176 276 2 47 88 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 176 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 176 276 4 23 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 176 276 (accept_3_4 91 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 176 276 2 45 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 176 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 89 176 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 176 276 4 22 44 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 176 276
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 87 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 176 276 2 43 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 176 276 (accept_3_4 85 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 176 276 4 21 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 176 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 83 176 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 176 276 2 41 88 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 176 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 176 276 4 20 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 176 276 (accept_3_4 79 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 176 276 2 39 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 176 276 (Polychromatic418967fa.accept_15_2_11_6_1_2135 77 176 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 176 276 4 19 44 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 176 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 176 276 2 37 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 176 276 (accept_3_4 73 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 176 276 4 18 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 176 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 71 176 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 176 276 2 35 88 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 176 276
  (Polychromatic418967fa.accept_13_4_7_3_1_92 69 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 176 276 4 17 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 176 276 (accept_3_4 67 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 176 276 2 33 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 176 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 176 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 176 276 4 16 44 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 176 276
  (Polychromatic418967fa.accept_13_11_7_3_1_894 63 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 176 276 2 31 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 176 276 (accept_3_4 61 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 176 276 4 15 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 176 276 (Polychromatic418967fa.accept_19_2_5_10_1_4608 59 176 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 176 276 2 29 88 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 176 276
  (Polychromatic418967fa.accept_9_3_5_6_1_253 57 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 176 276 4 14 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 176 276 (accept_3_4 55 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 176 276 2 27 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 176 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 176 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 176 276 4 13 44 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 176 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 176 276 2 25 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 176 276 (accept_3_4 49 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 176 276 4 12 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 176 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 176 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 176 276 2 23 88 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 176 276
  (Polychromatic418967fa.accept_17_11_6_4_1_4729 45 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 176 276 4 11 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 176 276 (accept_3_4 43 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 176 276 2 21 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 176 276 (Polychromatic418967fa.accept_19_3_5_10_1_6033 41 176 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 276 4 10 44 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 176 276 2 19 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 176 276 (accept_3_4 37 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 176 276 4 9 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 176 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 176 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 276 2 17 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 176 276 4 8 44 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 176 276 (accept_3_4 31
  176 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 176 276 2 15 88 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 176 276
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 176 276 4 7 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 176 276 (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 176 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 176 276 2 13 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 176 276 (accept_3_4 25 176 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 176 276 4 6 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 176 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 176 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 276 2 11 88 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 276
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 276 4 5 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 176 276 (accept_3_4 19 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  176 276 2 9 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 176 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 176 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 276 4 4 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 276
  (Polychromatic418967fa.accept_19_15_5_10_1_8925 15 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 176 276 2 7 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 176 276 (accept_3_4 13 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 176 276 4 3 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 176 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 176 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 276 2 5 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 9
  176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 276 4 2 44 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 276 (accept_3_4 7
  176 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 276 2 3 88 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 176 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 176 276 4 1 44 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 176 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 176 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 276 2 1 88 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 276 (accept_3_4 1 176 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 176
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 175 276 (Eq.refl Bool.true) (allA_succ_of_accept 101 175 276 (accept_3_5 101 175 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 175 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 100 175 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 175 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 99
  175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 175 276 (accept_3_5 98
  175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 175 276
  (Polychromatic418967fa.accept_9_7_4_6_1_273 97 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 175 276 (Polychromatic418967fa.accept_13_5_6_3_1_868 96 175 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 175 276 (accept_3_5 95 175 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 175 276 (Polychromatic418967fa.accept_10_4_5_6_1_651 94 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 175 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 93 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 175 276 (accept_3_5 92 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 175 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 91 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 175 276 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 175 276 (accept_3_5 89 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 175 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 88 175 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 175 276
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 87 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 175 276 (accept_3_5 86 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 175 276 (Polychromatic418967fa.accept_16_5_15_4_1_9099 85 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 175 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 84 175 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 175 276 (accept_3_5 83 175 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 175 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 82 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 175 276
  (Polychromatic418967fa.accept_10_1_5_6_1_649 81 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 175 276 (accept_3_5 80 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 175 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 79 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 175 276 (Polychromatic418967fa.accept_15_3_10_6_1_632 78 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 175 276 (accept_3_5 77 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 175 276 (Polychromatic418967fa.accept_15_1_10_6_1_631 76 175
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 175 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 75 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 175 276 (accept_3_5 74 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 175 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 73 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 175 276 (Polychromatic418967fa.accept_15_12_10_6_1_2134 72 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 175 276 (accept_3_5 71 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 175 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 175 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 175 276
  (Polychromatic418967fa.accept_10_9_5_6_1_691 69 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 175 276 (accept_3_5 68 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 175 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 175 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 175 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 175 276 (accept_3_5 65 175 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 175 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 175 276
  (Polychromatic418967fa.accept_15_3_10_6_1_632 63 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 175 276 (accept_3_5 62 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 175 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 175 276 (Polychromatic418967fa.accept_14_4_7_10_1_3888 60 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 175 276 (accept_3_5 59 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 175 276 (Polychromatic418967fa.accept_19_1_4_10_1_12988 58 175
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 175 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 175 276 (accept_3_5 56 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 175 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 175 276 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 175 276 (accept_3_5 53 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 175 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 175 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 175 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 51 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 175 276 (accept_3_5 50 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 175 276 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 175 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 175 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 276 (accept_3_5 47 175 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 175 276
  (Polychromatic418967fa.accept_14_3_7_10_1_2146 45 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 175 276 (accept_3_5 44 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 175 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 175 276 (Polychromatic418967fa.accept_11_9_10_1_1_581 42 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 175 276 (accept_3_5 41 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 175 276 (Polychromatic418967fa.accept_13_1_6_3_1_1547 40 175
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 175 276 (accept_3_5 38 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 175 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 175 276 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 276 (accept_3_5 35 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 175 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 175 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 276
  (Polychromatic418967fa.accept_15_3_10_6_1_632 33 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 276 (accept_3_5 32 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 276 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 175 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 175 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 276 (accept_3_5 29 175 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 175 276 (accept_3_5 26 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 175 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 175 276 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 276 (accept_3_5 23 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 276 (Polychromatic418967fa.accept_13_9_6_3_1_1514 22 175
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 175 276 (accept_3_5 20 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 175 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 276 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 276 (accept_3_5 17 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 175 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 276
  (Polychromatic418967fa.accept_19_15_4_10_1_11697 15 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 175 276 (accept_3_5 14 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 175 276 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 175 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 175 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 276 (accept_3_5 11 175 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 10
  175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 276
  (Polychromatic418967fa.accept_10_9_5_6_1_691 9 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 276 (accept_3_5 8 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 276 (Polychromatic418967fa.accept_17_6_5_4_1_7238 6 175 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 276 (accept_3_5 5 175 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 276 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 175 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 276 (accept_3_5 2 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 175 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 174 276 (Eq.refl Bool.true) (allA_succ_of_gcd 102 174 276 6 17 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 174 276 (Polychromatic418967fa.accept_9_2_3_6_1_88
  101 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 174 276 2 50 87 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 174 276 3 33 58
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 174 276 2 49
  87 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 174 276
  (Polychromatic418967fa.accept_9_7_3_6_1_270 97 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 174 276 6 16 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 174 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 95 174 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 174 276 2 47 87 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 174 276 3 31 58 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 174 276 2 46 87 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 174 276
  (Polychromatic418967fa.accept_9_1_3_6_1_70 91 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 174 276 6 15 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 174 276 (Polychromatic418967fa.accept_9_8_3_6_1_533 89 174 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 174 276 2 44 87 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 174 276 3 29 58 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 174 276 2 43 87 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 174 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 85 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 174 276 6 14 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 174 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 174 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 174 276 2 41 87 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 174 276 3 27 58 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 174 276 2 40 87 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 174 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 174 276 6 13 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 174 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 77 174 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 174 276 2 38 87 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 174 276 3 25 58 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 174 276 2 37 87 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 174 276
  (Polychromatic418967fa.accept_9_1_3_6_1_70 73 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 174 276 6 12 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 174 276 (Polychromatic418967fa.accept_9_8_3_6_1_533 71 174 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 174 276 2 35 87 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 174 276 3 23 58 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 174 276 2 34 87 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 174 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 174 276 6 11 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 174 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 174 276 2 32 87 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 174 276 3 21 58 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 174 276 2 31 87 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 174 276
  (Polychromatic418967fa.accept_9_7_3_6_1_270 61 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 276 6 10 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 59 174 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 174 276 2 29 87 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 174 276 3 19 58 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 174 276 2 28 87 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 174 276
  (Polychromatic418967fa.accept_9_1_3_6_1_70 55 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 276 6 9 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 174 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 174 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 276 2 26 87 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 174 276 3 17 58 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 174 276 2 25 87 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 276 6 8 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 174 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 174 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 276 2 23 87 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 174 276 3 15 58 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 174 276 2 22 87 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 276
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 276 6 7 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 174 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 174 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 276 2 20 87 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 174 276 3 13 58 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 174 276 2 19 87 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 276 6 6 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 174 276 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 174 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 276 2 17 87 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 174 276 3 11 58 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 174 276 2 16 87 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 276 6 5 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 174 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 174 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 276 2 14 87 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 174 276 3 9 58 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 174 276 2 13 87 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 276 6 4 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 174 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 174 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 276 2 11 87 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 174 276 3 7 58 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 174 276 2 10 87 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 276
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 276 6 3 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 174 276 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 174 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 276 2 8 87 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 174 276 3 5 58 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 174 276 2 7 87 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 276 6 2 29 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 174 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 174 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 276 2 5 87 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 174 276 3 3 58 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 174 276 2 4 87 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 7
  174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 276 6 1 29 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 276
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 174 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 174 276 2 2 87 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 174 276 3 1 58 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 174 276 2 1 87 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 174 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 174 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 174
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 173 276 (Eq.refl Bool.true) (allA_succ_of_accept 103 173 276 (accept_3_4 103 173 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 173 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 102 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 173 276
  (Polychromatic418967fa.accept_17_16_3_4_1_6010 101 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 173 276 (accept_3_4 100 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 173 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 99 173 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 173 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 98 173 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 173 276 (accept_3_4 97 173 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 173 276
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 96 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 173 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 95 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 173 276 (accept_3_4 94 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 173 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 173 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 92 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 173 276 (accept_3_4 91 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 173 276 (Polychromatic418967fa.accept_13_12_4_3_1_1528 90 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 173 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 89 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 173 276 (accept_3_4 88 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 173 276 (Polychromatic418967fa.accept_10_7_3_6_1_644 87 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 173 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 86 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 173 276 (accept_3_4 85 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 173 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 173 276 (Polychromatic418967fa.accept_20_3_13_16_1_641 83 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 173 276 (accept_3_4 82 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 173 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 173 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 173 276
  (Polychromatic418967fa.accept_9_8_2_6_1_875 80 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 173 276 (accept_3_4 79 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 173 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 173 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 77 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 173 276 (accept_3_4 76 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 173 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 173 276
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 74 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 173 276 (accept_3_4 73 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 173 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 173 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 173 276 (accept_3_4 70 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 173 276 (Polychromatic418967fa.accept_10_9_3_6_1_686 69 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 173 276
  (Polychromatic418967fa.accept_9_5_2_6_1_265 68 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 173 276 (accept_3_4 67 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 173 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 173 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 173 276 (accept_3_4 64 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 173 276 (Polychromatic418967fa.accept_19_6_2_10_1_4691 63 173 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 173 276
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 173 276 (accept_3_4 61 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 173 276 (Polychromatic418967fa.accept_16_12_13_4_1_3198 60 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 173 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 173 276 (accept_3_4 58 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 173 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 173 276
  (Polychromatic418967fa.accept_16_8_13_4_1_3258 56 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 173 276 (accept_3_4 55 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 173 276 (Polychromatic418967fa.accept_14_12_5_10_1_2130 54 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 173 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 173 276 (accept_3_4 52 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 173 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 173 276 (accept_3_4 49 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 173 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 173 276 (Polychromatic418967fa.accept_10_7_3_6_1_644 47 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 173 276 (accept_3_4 46 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 173 276 (Polychromatic418967fa.accept_22_1_19_12_1_13878 45
  173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 173 276 (accept_3_4 43 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 173 276 (Polychromatic418967fa.accept_22_20_19_12_1_12454 42 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 276 (accept_3_4 40 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 173 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 276
  (Polychromatic418967fa.accept_10_8_3_6_1_685 38 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 276 (accept_3_4 37 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 276 (accept_3_4 34 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 276
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 276 (accept_3_4 31 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 276 (accept_3_4 28 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 276 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 276
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 276 (accept_3_4 25 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 276 (Polychromatic418967fa.accept_16_8_13_4_1_3258 24 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 276 (accept_3_4 22 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 276
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 20 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 276 (accept_3_4 19 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 276 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 276 (accept_3_4 16 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 276
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 276 (accept_3_4 13 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 276 (Polychromatic418967fa.accept_19_11_2_10_1_8965 11 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 276 (accept_3_4 10 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 173 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 276 (accept_3_4 7 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 276 (Polychromatic418967fa.accept_16_6_13_4_1_643 6 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 276 (accept_3_4 4 173 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 173 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 276 (accept_3_4 1 173 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 172 276 (Eq.refl Bool.true) (allA_succ_of_gcd 104 172 276 4 26 43 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 172 276
  (Polychromatic418967fa.accept_9_4_1_6_1_284 103 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 172 276 2 51 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 172 276 (accept_3_5 101 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 172 276 4 25 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 172 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 99 172 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 172 276 2 49 86 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 172 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 97 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 172 276 4 24 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 172 276 (accept_3_5 95 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 172 276 2 47 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 172 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 93 172 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 172 276 4 23 43 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 172 276
  (Polychromatic418967fa.accept_10_1_2_6_1_638 91 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 172 276 2 45 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 172 276 (accept_3_5 89 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 172 276 4 22 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 172 276 (Polychromatic418967fa.accept_15_12_7_6_1_4013 87 172 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 172 276 2 43 86 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 172 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 85 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 172 276 4 21 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 172 276 (accept_3_5 83 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 172 276 2 41 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 172 276 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 172 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 172 276 4 20 43 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 172 276
  (Polychromatic418967fa.accept_9_7_1_6_1_261 79 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 172 276 2 39 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 172 276 (accept_3_5 77 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 172 276 4 19 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 172 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 75 172 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 172 276 2 37 86 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 172 276
  (Polychromatic418967fa.accept_15_13_7_6_1_682 73 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 172 276 4 18 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 172 276 (accept_3_5 71 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 172 276 2 35 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 172 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 172 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 172 276 4 17 43 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 172 276
  (Polychromatic418967fa.accept_9_4_1_6_1_284 67 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 172 276 2 33 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 172 276 (accept_3_5 65 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 172 276 4 16 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 172 276 (Polychromatic418967fa.accept_14_7_4_10_1_1351 63 172 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 172 276 2 31 86 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 172 276
  (Polychromatic418967fa.accept_9_7_1_6_1_261 61 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 172 276 4 15 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 172 276 (accept_3_5 59 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 172 276 2 29 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 172 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 172 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 172 276 4 14 43 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 172 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 172 276 2 27 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 172 276 (accept_3_5 53 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 172 276 4 13 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 172 276 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 172 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 172 276 2 25 86 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 172 276
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 172 276 4 12 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 172 276 (accept_3_5 47 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 172 276 2 23 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 172 276 (Polychromatic418967fa.accept_16_13_12_4_1_4323 45 172 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 172 276 4 11 43 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 172 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 172 276 2 21 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 172 276 (accept_3_5 41 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 172 276 4 10 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 172 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 172 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 276 2 19 86 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 276
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 37 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 276 4 9 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 172 276 (accept_3_5 35 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  172 276 2 17 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 172 276 (Polychromatic418967fa.accept_16_1_12_4_1_695 33 172 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 276 4 8 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 31
  172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 172 276 2 15 86 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 172 276 (accept_3_5 29
  172 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 172 276 4 7 43 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 172 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 172 276 2 13 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 172 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 172 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 172 276 4 6 43 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 172 276 (accept_3_5 23 172 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 172 276 2 11 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 172 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 276 4 5 43 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 276
  (Polychromatic418967fa.accept_16_3_12_4_1_170 19 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 172 276 2 9 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 172 276 (accept_3_5 17 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 172 276 4 4 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 172 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 172 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 276 2 7 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 13
  172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 172 276 4 3 43 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 172 276 (accept_3_5 11
  172 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 172 276 2 5 86 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 172 276
  (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 172 276 4 2 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 172 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 172 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 276 2 3 86 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 276 (accept_3_5 5 172 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172 276 4 1 43 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 172 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 172 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 172 276 2 1 86 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 172 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 172 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 172
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 171 276 (Eq.refl Bool.true) (allA_succ_of_gcd 105 171 276 3 35 57 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 171 276
  (Polychromatic418967fa.accept_11_5_6_1_1_988 104 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 171 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 103 171 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 171 276 3 34 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 171 276
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 101 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 171 276 (Polychromatic418967fa.accept_13_9_2_3_1_3027 100 171 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 171 276 3 33 57 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 171 276
  (Polychromatic418967fa.accept_18_8_9_6_1_3989 98 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 171 276 (Polychromatic418967fa.accept_10_7_1_6_1_673 97 171 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 171 276 3 32 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 171 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 95
  171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 171 276
  (Polychromatic418967fa.accept_22_6_17_12_1_7704 94 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 93 171 276 3 31 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 92 171 276 (Polychromatic418967fa.accept_10_2_1_6_1_634 92 171 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 171 276
  (Polychromatic418967fa.accept_14_7_3_10_1_1364 91 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 171 276 3 30 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 171 276 (Polychromatic418967fa.accept_13_11_2_3_1_883 89 171 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 171 276
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 88 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 171 276 3 29 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 171 276 (Polychromatic418967fa.accept_16_6_11_4_1_635 86 171 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 171 276
  (Polychromatic418967fa.accept_10_5_1_6_1_672 85 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 171 276 3 28 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 171 276 (Polychromatic418967fa.accept_13_5_2_3_1_1526 83 171 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 171 276
  (Polychromatic418967fa.accept_10_2_1_6_1_634 82 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 171 276 3 27 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 171 276 (Polychromatic418967fa.accept_18_8_9_6_1_3989 80 171 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 171 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 79 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 171 276 3 26 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 171 276 (Polychromatic418967fa.accept_10_7_1_6_1_673 77 171 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 171 276 (Polychromatic418967fa.accept_13_11_2_3_1_883
  76 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 171 276 3 25 57 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 171 276
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 74 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 171 276 (Polychromatic418967fa.accept_11_7_6_1_1_2182 73 171 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 171 276 3 24 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 171 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 71
  171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 276
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 70 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 171 276 3 23 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 171 276 (Polychromatic418967fa.accept_18_14_9_6_1_1777 68 171 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 171 276
  (Polychromatic418967fa.accept_10_7_1_6_1_673 67 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 171 276 3 22 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 171 276 (Polychromatic418967fa.accept_10_5_1_6_1_672 65 171 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 276
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 64 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 171 276 3 21 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 171 276 (Polychromatic418967fa.accept_10_2_1_6_1_634 62 171 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 276 (Polychromatic418967fa.accept_13_9_2_3_1_3027
  61 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 171 276 3 20 57 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 171 276
  (Polychromatic418967fa.accept_17_8_1_4_1_9831 59 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 171 276 (Polychromatic418967fa.accept_20_18_11_16_1_6973 58 171 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 171 276 3 19 57 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 171 276
  (Polychromatic418967fa.accept_16_8_11_4_1_3290 56 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 171 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 171 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 171 276 3 18 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 171 276 (Polychromatic418967fa.accept_13_1_2_3_1_911
  53 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 276
  (Polychromatic418967fa.accept_10_2_1_6_1_634 52 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 171 276 3 17 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 171 276 (Polychromatic418967fa.accept_13_11_2_3_1_883 50 171 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 276
  (Polychromatic418967fa.accept_11_5_6_1_1_988 49 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 171 276 3 16 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 171 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 171 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 276
  (Polychromatic418967fa.accept_20_6_11_16_1_3992 46 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 171 276 3 15 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 171 276 (Polychromatic418967fa.accept_13_5_2_3_1_1526 44 171 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 276
  (Polychromatic418967fa.accept_18_7_9_6_1_4023 43 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 171 276 3 14 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 171 276 (Polychromatic418967fa.accept_14_13_3_10_1_2159 41 171 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 276
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 171 276 3 13 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 171 276 (Polychromatic418967fa.accept_11_5_6_1_1_988 38 171 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 276 (Polychromatic418967fa.accept_10_7_1_6_1_673
  37 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 171 276 3 12 57 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 171 276
  (Polychromatic418967fa.accept_10_5_1_6_1_672 35 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 276 (Polychromatic418967fa.accept_14_6_3_10_1_3905 34 171 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 171 276 3 11 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 171 276 (Polychromatic418967fa.accept_10_2_1_6_1_634
  32 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 31 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 171 276 3 10 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 171 276 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 171 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 276
  (Polychromatic418967fa.accept_16_12_11_4_1_1359 28 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 171 276 3 9 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 171 276 (Polychromatic418967fa.accept_18_8_9_6_1_3989 26 171 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 276
  (Polychromatic418967fa.accept_10_5_1_6_1_672 25 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 171 276 3 8 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 171 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 171 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 276 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 171
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 171 276 3 7 57 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 171 276
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 20 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 171 276 (Polychromatic418967fa.accept_18_1_9_6_1_6630 19 171 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 171 276 3 6 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 276 (Polychromatic418967fa.accept_10_7_1_6_1_673
  17 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 276
  (Polychromatic418967fa.accept_11_5_6_1_1_988 16 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 171 276 3 5 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 171 276 (Polychromatic418967fa.accept_13_1_2_3_1_911 14 171 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 276 (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 171
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 276 3 4 57 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 276
  (Polychromatic418967fa.accept_13_11_2_3_1_883 11 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 276 (Polychromatic418967fa.accept_13_10_2_3_1_3025 10 171 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 276 3 3 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 276 (Polychromatic418967fa.accept_16_8_11_4_1_3290 8 171 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 7 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 171 276 3 2 57 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 171 276 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 171 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 276 (Polychromatic418967fa.accept_25_4_21_1_1_16962 4 171
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 276 3 1 57 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 276
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 171 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 276 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 171 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 171
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 170 276 (Eq.refl Bool.true) (allA_succ_of_gcd 106 170 276 2 53 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 170 276
  (Polychromatic418967fa.accept_11_6_5_1_1_586 105 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 170 276 2 52 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 170 276 (accept_3_4 103 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 170 276 2 51 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 170 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 101 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 170 276 2 50 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 170 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 99 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 170 276 2 49 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 170 276 (accept_3_4 97 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 170 276 2 48 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 170 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 95 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 170 276 2 47 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 170 276
  (Polychromatic418967fa.accept_9_3_8_6_1_80 93 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 170 276 2 46 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 170 276 (accept_3_4 91 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 170 276 2 45 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 170 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 89 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 170 276 2 44 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 170 276
  (Polychromatic418967fa.accept_15_12_5_6_1_2148 87 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 170 276 2 43 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 170 276 (accept_3_4 85 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 170 276 2 42 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 170 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 83 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 170 276 2 41 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 170 276
  (Polychromatic418967fa.accept_18_9_8_6_1_4021 81 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 170 276 2 40 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 170 276 (accept_3_4 79 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 170 276 2 39 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 170 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 77 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 170 276 2 38 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 170 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 170 276 2 37 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 170 276 (accept_3_4 73 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 170 276 2 36 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 170 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 170 276 2 35 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 170 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 170 276 2 34 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 170 276 (accept_3_4 67 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 170 276 2 33 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 170 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 65 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 170 276 2 32 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 170 276
  (Polychromatic418967fa.accept_13_11_1_3_1_910 63 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 170 276 2 31 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 170 276 (accept_3_4 61 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 170 276 2 30 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 170 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 170 276 2 29 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 170 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 170 276 2 28 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 170 276 (accept_3_4 55 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 170 276 2 27 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 170 276 (Polychromatic418967fa.accept_25_3_20_1_1_2743 53 170 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 276 2 26 85 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 276
  (Polychromatic418967fa.accept_21_9_2_3_1_11138 51 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 276 2 25 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 276 (accept_3_4 49 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 276 2 24 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 276 2 23 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 170 276
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 170 276 2 22 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 170 276 (accept_3_4 43 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 170 276 2 21 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 170 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 276 2 20 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 276
  (Polychromatic418967fa.accept_9_3_8_6_1_80 39 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 276 2 19 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 276 (accept_3_4 37 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 276 2 18 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 276 (Polychromatic418967fa.accept_20_15_10_16_1_8506 35 170 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 276 2 17 85 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 276 2 16 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 276 (accept_3_4 31 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 276 2 15 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 276 2 14 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 276 2 13 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 276 (accept_3_4 25 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 276 2 12 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 276 2 11 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 276
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 276 2 10 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 276 (accept_3_4 19 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 276 2 9 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 276 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 276 2 8 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 276 2 7 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 276 (accept_3_4 13 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 276 2 6 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 170 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 276 2 5 85 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 276
  (Polychromatic418967fa.accept_18_9_8_6_1_4021 9 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 276 2 4 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 276 (accept_3_4 7 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  276 2 3 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 170 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 276 2 2 85 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 170 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 276 2 1 85 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 276 (accept_3_4 1 170 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 169 276 (Eq.refl Bool.true) (allA_succ_of_accept 107 169 276 (accept_3_5 107 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 169 276 (Polychromatic418967fa.accept_22_18_15_12_1_7530 106
  169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 169 276
  (Polychromatic418967fa.accept_10_5_9_6_1_697 105 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 169 276 (accept_3_5 104 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 169 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 103 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 169 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 102 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 169 276 (accept_3_5 101 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 169 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 169
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 169 276
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 99 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 169 276 (accept_3_5 98 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 169 276 (Polychromatic418967fa.accept_19_2_17_10_1_4629 97 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 169 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 169 276 (accept_3_5 95 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 169 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 94 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 169 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 169 276 (accept_3_5 92 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 169 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 91 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 169 276 (Polychromatic418967fa.accept_17_5_16_4_1_4734 90 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 169 276 (accept_3_5 89 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 169 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 169 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 169 276
  (Polychromatic418967fa.accept_20_7_9_16_1_11410 87 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 169 276 (accept_3_5 86 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 169 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 85 169 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 169 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 84 169 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 169 276 (accept_3_5 83 169 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 169 276 (Polychromatic418967fa.accept_7_5_1_3_1_103
  82 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 169 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 169 276 (accept_3_5 80 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 169 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 169 276 (Polychromatic418967fa.accept_16_14_9_4_1_6693 78 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 169 276 (accept_3_5 77 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 169 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 76 169 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 169 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 169 276 (accept_3_5 74 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 169 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 169 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 169 276 (accept_3_5 71 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 169 276 (Polychromatic418967fa.accept_15_10_4_6_1_2129 70 169 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 169 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 69 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 169 276 (accept_3_5 68 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 169 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 169 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 66 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 169 276 (accept_3_5 65 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 169 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 64 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 169 276
  (Polychromatic418967fa.accept_10_3_9_6_1_94 63 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 169 276 (accept_3_5 62 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 169 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 169 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 169 276 (accept_3_5 59 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 169 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 276
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 169 276 (accept_3_5 56 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 169 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 169 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 276 (accept_3_5 53 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 169 276 (Polychromatic418967fa.accept_11_8_4_1_1_1000 52 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 169 276 (accept_3_5 50 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 169 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 169 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 276 (accept_3_5 47 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 169 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 45 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 169 276 (accept_3_5 44 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 169 276 (Polychromatic418967fa.accept_10_3_9_6_1_94 43 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 169 276 (Polychromatic418967fa.accept_19_4_17_10_1_4632 42 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 276 (accept_3_5 41 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 169 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 276 (accept_3_5 38 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 276 (Polychromatic418967fa.accept_21_15_1_3_1_9587 36 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 276 (accept_3_5 35 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 276 (Polychromatic418967fa.accept_19_15_17_10_1_8935 34
  169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 276 (accept_3_5 32 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 169 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 276 (accept_3_5 29 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 276
  (Polychromatic418967fa.accept_16_11_9_4_1_5438 27 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 276 (accept_3_5 26 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 276 (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 276 (accept_3_5 23 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 169 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 276 (accept_3_5 20 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 276 (accept_3_5 17 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 276
  (Polychromatic418967fa.accept_10_5_9_6_1_697 15 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 276 (accept_3_5 14 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 276 (accept_3_5 11 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 276 (accept_3_5 8 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 276 (Polychromatic418967fa.accept_19_7_17_10_1_4630 7 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 276 (Polychromatic418967fa.accept_21_6_1_3_1_3399 6 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 276 (accept_3_5 5 169 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 169 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 276
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 276 (accept_3_5 2 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 169 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 168 276 (Eq.refl Bool.true) (allA_succ_of_gcd 108 168 276 12 9 14 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 168 276
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 107 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 168 276 2 53 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 105 168 276 3 35 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 168 276 4 26 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 168 276 (Polychromatic418967fa.accept_10_3_8_6_1_326
  103 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 168 276 6 17 28 46
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 168 276
  (Polychromatic418967fa.accept_11_2_3_1_1_244 101 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 168 276 4 25 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 168 276 3 33 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 168 276 2 49 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 168 276 (Polychromatic418967fa.accept_16_1_8_4_1_4334 97 168
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 168 276 12 8 14 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 168 276
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 95 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 168 276 2 47 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 168 276 3 31 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 168 276 4 23 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 168 276 (Polychromatic418967fa.accept_15_1_3_6_1_621 91 168 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 168 276 6 15 28 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 168 276
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 89 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 168 276 4 22 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 168 276 3 29 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 168 276 2 43 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 168 276 (Polychromatic418967fa.accept_15_10_3_6_1_3042 85 168
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 168 276 12 7 14 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 168 276
  (Polychromatic418967fa.accept_10_3_8_6_1_326 83 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 168 276 2 41 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 168 276 3 27 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 168 276 4 20 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 168 276 (Polychromatic418967fa.accept_11_2_3_1_1_244 79 168 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 168 276 6 13 28 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 168 276
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 77 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 168 276 4 19 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 168 276 3 25 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 168 276 2 37 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 168 276 (Polychromatic418967fa.accept_10_3_8_6_1_326 73 168 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 168 276 12 6 14 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 168 276
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 71 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 168 276 2 35 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 168 276 3 23 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 168 276 4 17 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 168 276 (Polychromatic418967fa.accept_13_2_12_3_1_415 67 168
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 168 276 6 11 28 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 168 276
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 65 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 168 276 4 16 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 168 276 3 21 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 168 276 2 31 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 168 276 (Polychromatic418967fa.accept_13_9_12_3_1_907 61 168
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 168 276 12 5 14 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 168 276
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 59 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 168 276 2 29 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 168 276 3 19 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 168 276 4 14 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 276 (Polychromatic418967fa.accept_15_10_3_6_1_3042 55 168
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 168 276 6 9 28 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 168 276
  (Polychromatic418967fa.accept_10_3_8_6_1_326 53 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 168 276 4 13 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 168 276 3 17 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 168 276 2 25 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 276 (Polychromatic418967fa.accept_16_1_8_4_1_4334 49 168
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 168 276 12 4 14 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 168 276
  (Polychromatic418967fa.accept_16_15_8_4_1_1355 47 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 168 276 2 23 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 168 276 3 15 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 168 276 4 11 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 276 (Polychromatic418967fa.accept_10_3_8_6_1_326 43 168 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 168 276 6 7 28 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 168 276
  (Polychromatic418967fa.accept_13_2_12_3_1_415 41 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 168 276 4 10 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 168 276 3 13 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 168 276 2 19 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 276 (Polychromatic418967fa.accept_16_5_8_4_1_5418 37 168
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 168 276 12 3 14 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 168 276
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 168 276 2 17 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 168 276 3 11 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 168 276 4 8 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 168 276 (Polychromatic418967fa.accept_15_1_3_6_1_621 31 168 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 168 276 6 5 28 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 168 276
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 29 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 276 4 7 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 168 276 3 9 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 168 276 2 13 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 168 276 (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 168 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 276 12 2 14 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 276
  (Polychromatic418967fa.accept_10_3_8_6_1_326 23 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 168 276 2 11 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 168 276 3 7 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 168 276 4 5 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 168 276 (Polychromatic418967fa.accept_16_3_8_4_1_3279 19 168 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 276 6 3 28 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 276
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 168 276 4 4 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 168 276 3 5 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 168 276 2 7 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 168 276 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 168 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 276 12 1 14 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 276
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 168 276 2 5 84 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 168 276 3 3 56 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 168 276 4 2 42 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 168 276 (Polychromatic418967fa.accept_16_7_8_4_1_689 7 168 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 276 6 1 28 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 276 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5
  168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 276 4 1 42 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 168 276 3 1 56 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 168 276 2 1 84 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 276
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 168 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 167 276 (Eq.refl Bool.true) (allA_succ_of_accept 109 167 276 (accept_3_4 109 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 167 276 (Polychromatic418967fa.accept_16_12_7_4_1_687 108 167
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 167 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 107 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 167 276 (accept_3_4 106 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 167 276 (Polychromatic418967fa.accept_13_1_11_3_1_901 105 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 167 276 (Polychromatic418967fa.accept_16_8_7_4_1_2217 104 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 167 276 (accept_3_4 103 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 167 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 102 167
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 167 276
  (Polychromatic418967fa.accept_9_2_5_6_1_536 101 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 167 276 (accept_3_4 100 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 167 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 99 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 167 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 98 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 167 276 (accept_3_4 97 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 167 276 (Polychromatic418967fa.accept_13_5_11_3_1_902 96 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 167 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 95 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 167 276 (accept_3_4 94 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 167 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 167 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 92 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 167 276 (accept_3_4 91 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 167 276 (Polychromatic418967fa.accept_19_14_15_10_1_3359 90 167 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 167 276
  (Polychromatic418967fa.accept_9_8_5_6_1_538 89 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 167 276 (accept_3_4 88 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 167 276 (Polychromatic418967fa.accept_11_10_2_1_1_1036 87 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 167 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 86 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 167 276 (accept_3_4 85 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 167 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 167 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 83 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 167 276 (accept_3_4 82 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 167 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 167 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 80 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 167 276 (accept_3_4 79 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 167 276 (Polychromatic418967fa.accept_16_14_7_4_1_3243 78 167 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 167 276
  (Polychromatic418967fa.accept_16_13_7_4_1_3248 77 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 167 276 (accept_3_4 76 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 167 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 167 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 167 276 (accept_3_4 73 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 167 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 167 276
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 167 276 (accept_3_4 70 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 167 276 (Polychromatic418967fa.accept_11_3_2_1_1_994 69 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 167 276 (Polychromatic418967fa.accept_15_8_2_6_1_2125 68 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 167 276 (accept_3_4 67 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 167 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 167 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 167 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 167 276 (accept_3_4 64 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 167 276 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 167 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 62 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 167 276 (accept_3_4 61 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 167 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 167 276 (accept_3_4 58 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 167 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 167 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 56 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 276 (accept_3_4 55 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 167 276 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 167 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 167 276 (accept_3_4 52 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 167 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 167 276 (Polychromatic418967fa.accept_26_24_11_16_1_16963 50 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 276 (accept_3_4 49 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 167 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 276
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 167 276 (accept_3_4 46 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 167 276 (Polychromatic418967fa.accept_14_3_13_10_1_761 45 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 167 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 276 (accept_3_4 43 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 276 (Polychromatic418967fa.accept_15_12_2_6_1_2127 42 167 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 276
  (Polychromatic418967fa.accept_10_1_7_6_1_91 41 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 167 276 (accept_3_4 40 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 167 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 167 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 276 (accept_3_4 37 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 276 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 276 (accept_3_4 34 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 276 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 276 (accept_3_4 31 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 276
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 276 (accept_3_4 28 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 167 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 276 (accept_3_4 25 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 276 (Polychromatic418967fa.accept_16_8_7_4_1_2217 24 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 167 276 (accept_3_4 22 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 167 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 167 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 276 (accept_3_4 19 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 276
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 276 (accept_3_4 16 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 276 (Polychromatic418967fa.accept_13_2_11_3_1_873 15 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 276 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 276 (accept_3_4 13 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 167 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 276 (accept_3_4 10 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 276 (accept_3_4 7 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 276 (Polychromatic418967fa.accept_19_6_15_10_1_2170 6 167 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 276
  (Polychromatic418967fa.accept_13_5_11_3_1_902 5 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 276 (accept_3_4 4 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 167 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 276 (accept_3_4 1 167 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 166 276 (Eq.refl Bool.true) (allA_succ_of_gcd 110 166 276 2 55 83 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 166 276
  (Polychromatic418967fa.accept_9_1_4_6_1_5 109 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 166 276 2 54 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 166 276 (accept_3_5 107 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 166 276 2 53 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 166 276 (Polychromatic418967fa.accept_17_3_13_4_1_8530 105 166 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 166 276 2 52 83 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 166 276
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 103 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 166 276 2 51 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 166 276 (accept_3_5 101 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 166 276 2 50 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 166 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 99 166 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 166 276 2 49 83 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 166 276
  (Polychromatic418967fa.accept_9_7_4_6_1_273 97 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 166 276 2 48 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 166 276 (accept_3_5 95 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 166 276 2 47 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 166 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 166 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 166 276 2 46 83 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 166 276
  (Polychromatic418967fa.accept_9_1_4_6_1_5 91 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 166 276 2 45 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 166 276 (accept_3_5 89 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 166 276 2 44 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 166 276 (Polychromatic418967fa.accept_18_15_4_6_1_1763 87 166 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 166 276 2 43 83 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 166 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 85 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 166 276 2 42 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 166 276 (accept_3_5 83 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 166 276 2 41 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 166 276 (Polychromatic418967fa.accept_19_5_14_10_1_8933 81 166 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 166 276 2 40 83 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 166 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 79 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 166 276 2 39 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 166 276 (accept_3_5 77 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 166 276 2 38 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 166 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 75 166 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 166 276 2 37 83 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 166 276
  (Polychromatic418967fa.accept_9_1_4_6_1_5 73 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 166 276 2 36 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 166 276 (accept_3_5 71 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 166 276 2 35 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 166 276 (Polychromatic418967fa.accept_15_9_1_6_1_657 69 166 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 166 276 2 34 83 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 166 276
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 67 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 166 276 2 33 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 166 276 (accept_3_5 65 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 166 276 2 32 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 166 276 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 166 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 166 276 2 31 83 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 166 276
  (Polychromatic418967fa.accept_9_7_4_6_1_273 61 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 166 276 2 30 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 166 276 (accept_3_5 59 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 166 276 2 29 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 166 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 166 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 166 276 2 28 83 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 166 276
  (Polychromatic418967fa.accept_9_1_4_6_1_5 55 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 166 276 2 27 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 166 276 (accept_3_5 53 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 276 2 26 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 166 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 276 2 25 83 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 276
  (Polychromatic418967fa.accept_25_24_16_1_1_9898 49 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 166 276 2 24 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 166 276 (accept_3_5 47 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 276 2 23 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 276 (Polychromatic418967fa.accept_13_6_10_3_1_897 45 166 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 276 2 22 83 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 276 2 21 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 276 (accept_3_5 41 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 276 2 20 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 166 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 276 2 19 83 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 276 2 18 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 276 (accept_3_5 35 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 276 2 17 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 276 (Polychromatic418967fa.accept_13_7_10_3_1_1505 33 166 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 276 2 16 83 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 276
  (Polychromatic418967fa.accept_17_14_13_4_1_13402 31 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 166 276 2 15 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 166 276 (accept_3_5 29 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 276 2 14 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 276 (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 166 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 276 2 13 83 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 276
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 276 2 12 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 276 (accept_3_5 23 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 276 2 11 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 166 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 276 2 10 83 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 276
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 276 2 9 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 276 (accept_3_5 17 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 276 2 8 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 166 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 276 2 7 83 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 276
  (Polychromatic418967fa.accept_16_13_6_4_1_3277 13 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 166 276 2 6 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 166 276 (accept_3_5 11 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 276 2 5 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 166 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 276 2 4 83 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 276
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 276 2 3 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 276 (accept_3_5 5 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  276 2 2 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 166 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 276 2 1 83 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 166 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 165 276 (Eq.refl Bool.true) (allA_succ_of_gcd 111 165 276 3 37 55 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 110 165 276
  (Polychromatic418967fa.accept_9_2_3_6_1_88 110 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 165 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 109 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 165 276 3 36 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 165 276 (Polychromatic418967fa.accept_9_8_3_6_1_533
  107 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 165 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 106 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 165 276 3 35 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 165 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 104 165 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 165 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 103 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 165 276 3 34 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 165 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 101 165 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 165 276 (Polychromatic418967fa.accept_9_1_3_6_1_70
  100 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 165 276 3 33 55 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 165 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 98 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 165 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 165 276 3 32 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 165 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 95
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 165 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 94 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 165 276 3 31 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 165 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 92 165 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 165 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 91
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 165 276 3 30 55 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 165 276
  (Polychromatic418967fa.accept_8_1_5_4_1_388 89 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 165 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 88 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 165 276 3 29 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 165 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 86
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 165 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 85 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 165 276 3 28 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 165 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 83 165 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 165 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 82
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 165 276 3 27 55 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 165 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 80 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 165 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 165 276 3 26 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 165 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 77
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 165 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 76 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 165 276 3 25 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 165 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 165 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 165 276 (Polychromatic418967fa.accept_8_1_5_4_1_388
  73 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 165 276 3 24 55 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 165 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 165 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 165 276 3 23 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 165 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 165 276 3 22 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 165 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 65 165 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 165 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 64
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 165 276 3 21 55 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 165 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 165 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 165 276 3 20 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 165 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 165 276 3 19 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 165 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 165 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 276 (Polychromatic418967fa.accept_7_6_4_3_1_266
  55 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 165 276 3 18 55 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 165 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 165 276 3 17 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 165 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 50
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 276
  (Polychromatic418967fa.accept_8_1_5_4_1_388 49 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 165 276 3 16 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 165 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 165 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 46
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 165 276 3 15 55 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 165 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 165 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 165 276 3 14 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 165 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 41
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 165 276 3 13 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 165 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 165 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 165 276 3 12 55 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 165 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 165 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 276 3 11 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 165 276 3 10 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 165 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 165 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 165 276 3 9 55 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 165 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 165 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 165 276 3 8 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 23
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 22 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 165 276 3 7 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 165 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 165 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 276 3 6 55 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 276
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 276 3 5 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 165 276 3 4 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 165 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 165 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 165 276 3 3 55 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 276 3 2 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 165 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 165 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 165 276 3 1 55 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 165 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 165 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 165 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 164 276 (Eq.refl Bool.true) (allA_succ_of_gcd 112 164 276 4 28 41 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 164 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 111 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 164 276 2 55 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 164 276 (accept_3_4 109 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 164 276 4 27 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 164 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 107 164 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 164 276 2 53 82 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 164 276
  (Polychromatic418967fa.accept_10_5_4_6_1_319 105 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 164 276 4 26 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 164 276 (accept_3_4 103 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 164 276 2 51 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 164 276 (Polychromatic418967fa.accept_11_2_10_1_1_1017 101 164 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 164 276 4 25 41 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 164 276
  (Polychromatic418967fa.accept_15_9_14_6_1_3004 99 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 164 276 2 49 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 164 276 (accept_3_4 97 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 164 276 4 24 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 164 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 95 164 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 164 276 2 47 82 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 164 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 93 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 164 276 4 23 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 164 276 (accept_3_4 91 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 164 276 2 45 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 164 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 89 164 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 164 276 4 22 41 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 164 276
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 87 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 164 276 2 43 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 164 276 (accept_3_4 85 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 164 276 4 21 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 164 276 (Polychromatic418967fa.accept_13_5_8_3_1_1535 83 164 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 164 276 2 41 82 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 164 276
  (Polychromatic418967fa.accept_18_9_2_6_1_9322 81 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 164 276 4 20 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 164 276 (accept_3_4 79 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 164 276 2 39 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 164 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 77 164 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 164 276 4 19 41 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 164 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 75 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 164 276 2 37 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 164 276 (accept_3_4 73 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 164 276 4 18 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 164 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 71 164 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 164 276 2 35 82 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 164 276
  (Polychromatic418967fa.accept_15_9_14_6_1_3004 69 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 164 276 4 17 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 164 276 (accept_3_4 67 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 164 276 2 33 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 164 276 (Polychromatic418967fa.accept_10_5_4_6_1_319 65 164 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 164 276 4 16 41 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 276
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 63 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 164 276 2 31 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 164 276 (accept_3_4 61 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 276 4 15 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 164 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 276 2 29 82 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 57 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 276 4 14 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 276 (accept_3_4 55 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 276 2 27 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 164 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 276 4 13 41 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 276
  (Polychromatic418967fa.accept_21_9_17_3_1_6408 51 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 276 2 25 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 276 (accept_3_4 49 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 276 4 12 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 276 (Polychromatic418967fa.accept_19_9_12_10_1_10393 47 164 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 276 2 23 82 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 276
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 164 276 4 11 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 164 276 (accept_3_4 43 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 276 2 21 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 164 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 276 4 10 41 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 276 2 19 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 276 (accept_3_4 37 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 276 4 9 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 164 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 164 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 276 2 17 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 276 (Polychromatic418967fa.accept_13_7_8_3_1_1533
  33 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 164 276 4 8 41 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 164 276
  (accept_3_4 31 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 164 276 2 15 82 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 164 276
  (Polychromatic418967fa.accept_21_8_17_3_1_8031 29 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 164 276 4 7 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 164 276 (Polychromatic418967fa.accept_17_10_11_4_1_2522 27 164 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 164 276 2 13 82 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 164 276 (accept_3_4 25 164 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 164 276 4 6 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 164 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 23
  164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 276 2 11 82 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 276 4 5 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 164 276 (accept_3_4 19 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  164 276 2 9 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 164 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 164 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 276 4 4 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 276 (Polychromatic418967fa.accept_10_5_4_6_1_319
  15 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 276 2 7 82 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 276
  (accept_3_4 13 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 276 4 3 41 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 276
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 164 276 2 5 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 164 276 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 164 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 276 4 2 41 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 276 (accept_3_4 7 164 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164 276 2 3 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 164 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 164 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 164 276 4 1 41 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 164 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 164 276 2 1 82 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 164 276 (accept_3_4 1 164 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 163 276 (Eq.refl Bool.true) (allA_succ_of_accept 113 163 276 (accept_3_5 113 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 163 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 112 163
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 163 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 111 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 163 276 (accept_3_5 110 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 163 276 (Polychromatic418967fa.accept_10_9_3_6_1_686 109 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 163 276 (Polychromatic418967fa.accept_10_8_3_6_1_685 108 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 163 276 (accept_3_5 107 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 163 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 106 163
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 163 276
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 105 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 163 276 (accept_3_5 104 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 163 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 103 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 163 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 102 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 163 276 (accept_3_5 101 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 163 276 (Polychromatic418967fa.accept_13_9_7_3_1_1531 100 163
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 163 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 99 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 163 276 (accept_3_5 98 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 163 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 163 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 163 276 (accept_3_5 95 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 163 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 94 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 163 276
  (Polychromatic418967fa.accept_9_3_1_6_1_86 93 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 163 276 (accept_3_5 92 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 163 276 (Polychromatic418967fa.accept_17_6_10_4_1_6007 91 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 163 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 163 276 (accept_3_5 89 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 163 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 88 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 163 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 87 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 163 276 (accept_3_5 86 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 163 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 163 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 84 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 163 276 (accept_3_5 83 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 163 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 163 276
  (Polychromatic418967fa.accept_16_1_3_4_1_665 81 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 163 276 (accept_3_5 80 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 163 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 79 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 163 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 163 276 (accept_3_5 77 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 163 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 163 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 163 276 (accept_3_5 74 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 163 276 (Polychromatic418967fa.accept_13_8_7_3_1_430 73 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 163 276 (Polychromatic418967fa.accept_16_8_3_4_1_3233 72 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 163 276 (accept_3_5 71 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 163 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 163 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 163 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 163 276 (accept_3_5 68 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 163 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 163 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 66 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 276 (accept_3_5 65 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 63 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 163 276 (accept_3_5 62 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 163 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 163 276 (Polychromatic418967fa.accept_13_8_7_3_1_430 60 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 163 276 (accept_3_5 59 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 163 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 163 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 163 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 163 276 (accept_3_5 56 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 163 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 163 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 163 276 (accept_3_5 53 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 163 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 163 276
  (Polychromatic418967fa.accept_21_9_16_3_1_11133 51 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 163 276 (accept_3_5 50 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 163 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 163 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 163 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 276 (accept_3_5 47 163 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 276
  (Polychromatic418967fa.accept_19_8_11_10_1_14236 46 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 276 (Polychromatic418967fa.accept_17_11_10_4_1_5955 45 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 276 (accept_3_5 44 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 163 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 276
  (Polychromatic418967fa.accept_22_20_9_12_1_12416 42 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 163 276 (accept_3_5 41 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 163 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 163 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 163 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 276 (accept_3_5 38 163 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 276 (Polychromatic418967fa.accept_10_7_3_6_1_644
  37 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 276 (accept_3_5 35 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 276 (accept_3_5 32 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 276
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 163 276 (accept_3_5 29 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 163 276 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 163 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 276 (accept_3_5 26 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 276
  (Polychromatic418967fa.accept_13_11_7_3_1_894 24 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 276 (accept_3_5 23 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 276 (accept_3_5 20 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 276
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 276 (accept_3_5 17 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 276 (accept_3_5 14 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 276 (accept_3_5 11 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 276 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 276 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 276 (accept_3_5 8 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 276 (accept_3_5 5 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 163 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 276 (accept_3_5 2 163 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 163 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 162 276 (Eq.refl Bool.true) (allA_succ_of_gcd 114 162 276 6 19 27 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 162 276
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 113 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 162 276 2 56 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 162 276 3 37 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 162 276 2 55 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 162 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 109 162
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 162 276 6 18 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 162 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 107 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 162 276 2 53 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 162 276 3 35 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 162 276 2 52 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 162 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 103 162
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 162 276 6 17 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 162 276
  (Polychromatic418967fa.accept_10_1_2_6_1_638 101 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 162 276 2 50 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 162 276 3 33 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 162 276 2 49 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 162 276 (Polychromatic418967fa.accept_15_7_12_6_1_1327 97 162
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 162 276 6 16 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 162 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 95 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 162 276 2 47 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 162 276 3 31 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 162 276 2 46 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 162 276 (Polychromatic418967fa.accept_10_1_2_6_1_638 91 162 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 162 276 6 15 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 162 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 89 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 162 276 2 44 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 162 276 3 29 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 162 276 2 43 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 162 276 (Polychromatic418967fa.accept_15_10_12_6_1_3000 85 162
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 162 276 6 14 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 162 276
  (Polychromatic418967fa.accept_13_5_6_3_1_868 83 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 162 276 2 41 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 162 276 3 27 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 162 276 2 40 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 162 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 162 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 162 276 6 13 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 162 276
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 77 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 162 276 2 38 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 162 276 3 25 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 162 276 2 37 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 162 276 (Polychromatic418967fa.accept_21_10_15_3_1_6431 73 162
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 162 276 6 12 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 162 276
  (Polychromatic418967fa.accept_10_1_2_6_1_638 71 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 162 276 2 35 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 162 276 3 23 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 162 276 2 34 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 162 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 162 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 162 276 6 11 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 162 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 162 276 2 32 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 162 276 3 21 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 162 276 2 31 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 162 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 162 276 6 10 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 162 276
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 162 276 2 29 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 162 276 3 19 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 162 276 2 28 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 276 (Polychromatic418967fa.accept_15_10_12_6_1_3000 55 162
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 162 276 6 9 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 162 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 162 276 2 26 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 162 276 3 17 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 162 276 2 25 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 276 (Polychromatic418967fa.accept_13_10_6_3_1_1515 49 162
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 162 276 6 8 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 162 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 162 276 2 23 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 162 276 3 15 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 162 276 2 22 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 276 (Polychromatic418967fa.accept_21_1_15_3_1_4817 43 162
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 162 276 6 7 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 162 276
  (Polychromatic418967fa.accept_10_1_2_6_1_638 41 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 162 276 2 20 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 162 276 3 13 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 162 276 2 19 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 162 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 162 276 6 6 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 162 276
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 162 276 2 17 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 162 276 3 11 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 162 276 2 16 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 276 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 162 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 162 276 6 5 27 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 162 276
  (Polychromatic418967fa.accept_17_12_9_4_1_5982 29 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 162 276 2 14 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 162 276 3 9 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 162 276 2 13 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 162 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 162 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 162 276 6 4 27 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 162 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 162 276 2 11 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 162 276 3 7 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 162 276 2 10 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 162 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 162 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 162 276 6 3 27 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 162 276
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 162 276 2 8 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 162 276 3 5 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 162 276 2 7 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 162 276 (Polychromatic418967fa.accept_17_13_9_4_1_5979 13 162 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 276 6 2 27 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 276 2 5 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 162 276 3 3 54 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 162 276 2 4 81 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 162 276 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 162 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 276 6 1 27 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 5
  162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 276 2 2 81 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 162 276 3 1 54 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 162 276 2 1 81 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 276
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 162 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 162
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 161 276 (Eq.refl Bool.true) (allA_succ_of_gcd 115 161 276 23 5 7 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 114 161 276
  (Polychromatic418967fa.accept_15_9_11_6_1_637 114 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 161 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 113 161 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 161 276 (accept_3_4 112 161 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 161 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 111 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 161 276
  (Polychromatic418967fa.accept_9_2_8_6_1_79 110 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 161 276 (accept_3_4 109 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 161 276 (Polychromatic418967fa.accept_15_3_11_6_1_3083 108 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 161 276 (Polychromatic418967fa.accept_10_7_1_6_1_673 107 161 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 161 276 (accept_3_4 106 161 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 161 276 (Polychromatic418967fa.accept_10_5_1_6_1_672
  105 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 161 276
  (Polychromatic418967fa.accept_9_5_8_6_1_281 104 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 161 276 (accept_3_4 103 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 161 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 102 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 161 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 101 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 161 276 (accept_3_4 100 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 161 276 (Polychromatic418967fa.accept_13_8_5_3_1_427 99 161
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 161 276
  (Polychromatic418967fa.accept_17_13_8_4_1_2514 98 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 161 276 (accept_3_4 97 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 161 276 (Polychromatic418967fa.accept_19_1_9_10_1_10391 96 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 161 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 95 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 161 276 (accept_3_4 94 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 161 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 93 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 161 276 23 4 7 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 161 276 (accept_3_4 91 161 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 161 276
  (Polychromatic418967fa.accept_21_6_14_3_1_4932 90 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 161 276 (Polychromatic418967fa.accept_13_11_5_3_1_889 89 161 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 161 276 (accept_3_4 88 161 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 161 276 (Polychromatic418967fa.accept_10_7_1_6_1_673 87 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 161 276
  (Polychromatic418967fa.accept_9_5_8_6_1_281 86 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 161 276 (accept_3_4 85 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 161 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 84 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 161 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 83 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 161 276 (accept_3_4 82 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 161 276 (Polychromatic418967fa.accept_14_11_7_10_1_4852 81 161 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 161 276
  (Polychromatic418967fa.accept_13_2_5_3_1_406 80 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 161 276 (accept_3_4 79 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 161 276 (Polychromatic418967fa.accept_15_3_11_6_1_3083 78 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 161 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 77 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 161 276 (accept_3_4 76 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 161 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 161 276
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 161 276 (accept_3_4 73 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 161 276 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 161 276 (Polychromatic418967fa.accept_13_6_5_3_1_426 71 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 276 (accept_3_4 70 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 161 276 23 3 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 161 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 68
  161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 161 276 (accept_3_4 67
  161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 161 276
  (Polychromatic418967fa.accept_9_3_8_6_1_80 66 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 161 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 65 161 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 276 (accept_3_4 64 161 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 161 276 (Polychromatic418967fa.accept_13_11_5_3_1_889 63 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 276
  (Polychromatic418967fa.accept_10_2_1_6_1_634 62 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 161 276 (accept_3_4 61 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 161 276 (Polychromatic418967fa.accept_13_8_5_3_1_427 60 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 161 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 276 (accept_3_4 58 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 276
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 276 (accept_3_4 55 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 276 (Polychromatic418967fa.accept_13_2_5_3_1_406 54 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 276 (accept_3_4 52 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 276 (Polychromatic418967fa.accept_16_3_1_4_1_5426 51 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 276
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 276 (accept_3_4 49 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 161 276 23 2 7 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 161 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 45 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 161 276 (Polychromatic418967fa.accept_16_12_1_4_1_5403 44 161 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 276 (accept_3_4 43 161 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 161 276 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 161 276
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 161 276 (accept_3_4 40 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 161 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 161 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 276 (accept_3_4 37 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 161 276 (Polychromatic418967fa.accept_21_15_14_3_1_9677 36 161 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 161 276
  (Polychromatic418967fa.accept_10_5_1_6_1_672 35 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 161 276 (accept_3_4 34 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 161 276 (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 161 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 276 (accept_3_4 31 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 161 276 (accept_3_4 28 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 161 276 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 161 276 (Polychromatic418967fa.accept_19_7_9_10_1_4600 26 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 276 (accept_3_4 25 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 276 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 161
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 23 161 276 23 1 7 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 22 161 276 (accept_3_4 22
  161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 161 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 161 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 276 (accept_3_4 19 161 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 161 276 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 276
  (Polychromatic418967fa.accept_10_7_1_6_1_673 17 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 276 (accept_3_4 16 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 276 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 276 (accept_3_4 13 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 276
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 276 (accept_3_4 10 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 276 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 276 (Polychromatic418967fa.accept_13_8_5_3_1_427 8 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 276 (accept_3_4 7 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 276 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 161 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 276 (accept_3_4 4 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 161 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 276 (accept_3_4 1 161 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 160 276 (Eq.refl Bool.true) (allA_succ_of_gcd 116 160 276 4 29 40 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 160 276
  (Polychromatic418967fa.accept_11_5_6_1_1_988 115 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 160 276 2 57 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 160 276 (accept_3_5 113 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 160 276 4 28 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 160 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 111 160 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 160 276 2 55 80 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 160 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 109 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 160 276 4 27 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 160 276 (accept_3_5 107 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 160 276 2 53 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 160 276 (Polychromatic418967fa.accept_13_1_4_3_1_1545 105 160 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 160 276 4 26 40 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 160 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 103 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 160 276 2 51 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 160 276 (accept_3_5 101 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 160 276 4 25 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 160 276 (Polychromatic418967fa.accept_17_14_7_4_1_3476 99 160 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 160 276 2 49 80 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 160 276
  (Polychromatic418967fa.accept_17_12_7_4_1_7231 97 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 160 276 4 24 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 160 276 (accept_3_5 95 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 160 276 2 47 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 160 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 160 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 160 276 4 23 40 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 160 276
  (Polychromatic418967fa.accept_9_1_7_6_1_75 91 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 160 276 2 45 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 160 276 (accept_3_5 89 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 160 276 4 22 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 160 276 (Polychromatic418967fa.accept_14_3_6_10_1_752 87 160 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 160 276 2 43 80 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 160 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 85 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 160 276 4 21 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 160 276 (accept_3_5 83 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 160 276 2 41 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 160 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 160 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 160 276 4 20 40 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 160 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 160 276 2 39 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 160 276 (accept_3_5 77 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 160 276 4 19 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 160 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 75 160 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 160 276 2 37 80 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 160 276
  (Polychromatic418967fa.accept_9_1_7_6_1_75 73 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 160 276 4 18 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 160 276 (accept_3_5 71 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 160 276 2 35 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 160 276 (Polychromatic418967fa.accept_18_15_16_6_1_1751 69 160 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 160 276 4 17 40 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 160 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 160 276 2 33 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 160 276 (accept_3_5 65 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 160 276 4 16 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 160 276 (Polychromatic418967fa.accept_15_3_10_6_1_632 63 160 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 160 276 2 31 80 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 160 276
  (Polychromatic418967fa.accept_15_1_10_6_1_631 61 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 160 276 4 15 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 160 276 (accept_3_5 59 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 160 276 2 29 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 160 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 160 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 160 276 4 14 40 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 160 276
  (Polychromatic418967fa.accept_9_1_7_6_1_75 55 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 160 276 2 27 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 160 276 (accept_3_5 53 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 160 276 4 13 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 160 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 160 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 276 2 25 80 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 160 276 4 12 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 160 276 (accept_3_5 47 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 160 276 2 23 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 160 276 (Polychromatic418967fa.accept_14_3_6_10_1_752 45 160 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 160 276 4 11 40 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 160 276
  (Polychromatic418967fa.accept_19_5_8_10_1_8978 43 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 160 276 2 21 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 160 276 (accept_3_5 41 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 160 276 4 10 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 160 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 160 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 276 2 19 80 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 160 276 4 9 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 160 276 (accept_3_5 35 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  160 276 2 17 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 160 276 (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 160 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 160 276 4 8 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 160 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 31
  160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 276 2 15 80 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 276 (accept_3_5 29
  160 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 160 276 4 7 40 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 160 276
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 160 276 2 13 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 160 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 160 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 160 276 4 6 40 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 160 276 (accept_3_5 23 160 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 160 276 2 11 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 160 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 276 4 5 40 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 276
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 160 276 2 9 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 160 276 (accept_3_5 17 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 160 276 4 4 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 160 276 (Polychromatic418967fa.accept_18_15_16_6_1_1751 15 160 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 160 276 2 7 80 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 160 276 4 3 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 160 276 (accept_3_5 11 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  160 276 2 5 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 160 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 160 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 276 4 2 40 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 276 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 160 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 276 2 3 80 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 276 (accept_3_5 5
  160 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 276 4 1 40 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 160 276
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 160 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 160 276 2 1 80 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 160 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 160 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 160
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 159 276 (Eq.refl Bool.true) (allA_succ_of_gcd 117 159 276 3 39 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 159 276
  (Polychromatic418967fa.accept_11_6_5_1_1_586 116 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 159 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 115 159 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 159 276 3 38 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 159 276 (Polychromatic418967fa.accept_7_1_5_3_1_268
  113 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 159 276
  (Polychromatic418967fa.accept_17_10_6_4_1_2506 112 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 111 159 276 3 37 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 110 159 276 (Polychromatic418967fa.accept_14_12_5_10_1_2130 110 159 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 159 276
  (Polychromatic418967fa.accept_15_4_9_6_1_627 109 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 159 276 3 36 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 159 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 107 159 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 159 276 (Polychromatic418967fa.accept_7_1_5_3_1_268
  106 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 159 276 3 35 53 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 159 276
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 104 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 159 276 (Polychromatic418967fa.accept_10_3_9_6_1_94 103 159 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 159 276 3 34 53 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 159 276
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 101 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 159 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 159 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 159 276 3 33 53 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 159 276
  (Polychromatic418967fa.accept_19_3_7_10_1_6023 98 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 159 276 (Polychromatic418967fa.accept_20_17_19_16_1_6996 97 159 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 159 276 3 32 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 159 276
  (Polychromatic418967fa.accept_10_5_9_6_1_697 95 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 159 276 (Polychromatic418967fa.accept_11_6_5_1_1_586 94 159 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 159 276 3 31 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 159 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 92
  159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 159 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 91 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 159 276 3 30 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 159 276 (Polychromatic418967fa.accept_15_14_9_6_1_5093 89 159 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 159 276
  (Polychromatic418967fa.accept_16_8_15_4_1_5402 88 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 159 276 3 29 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 159 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 86 159 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 276 (Polychromatic418967fa.accept_7_1_5_3_1_268
  85 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 159 276 3 28 53 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 159 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 83 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 159 276 (Polychromatic418967fa.accept_14_12_5_10_1_2130 82 159 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 159 276 3 27 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 159 276
  (Polychromatic418967fa.accept_21_17_12_3_1_4848 80 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 159 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 159 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 159 276 3 26 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 159 276
  (Polychromatic418967fa.accept_18_5_15_6_1_3999 77 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 159 276 (Polychromatic418967fa.accept_15_1_9_6_1_1323 76 159 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 159 276 3 25 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 159 276 (Polychromatic418967fa.accept_15_14_9_6_1_5093
  74 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 276
  (Polychromatic418967fa.accept_10_3_9_6_1_94 73 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 159 276 3 24 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 159 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 159 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 276 (Polychromatic418967fa.accept_17_2_6_4_1_2431
  70 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 159 276 3 23 53 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 159 276
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 68 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 159 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 159 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 159 276 3 22 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 159 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 159 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 159 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 159 276 3 21 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 159 276
  (Polychromatic418967fa.accept_16_14_15_4_1_3268 62 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 159 276 (Polychromatic418967fa.accept_11_6_5_1_1_586 61 159 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 159 276 3 20 53 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 159 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 159 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 159 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 159 276 3 19 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 159 276 (Polychromatic418967fa.accept_15_11_9_6_1_1321
  56 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 276
  (Polychromatic418967fa.accept_10_5_9_6_1_697 55 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 159 276 3 18 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 159 276 (Polychromatic418967fa.accept_10_3_9_6_1_94 53 159 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 276
  (Polychromatic418967fa.accept_18_16_15_6_1_4039 52 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 159 276 3 17 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 159 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 159 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 276
  (Polychromatic418967fa.accept_15_4_9_6_1_627 49 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 159 276 3 16 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 159 276 (Polychromatic418967fa.accept_18_11_15_6_1_2832 47 159 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 276
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 46 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 159 276 3 15 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 159 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 159 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 276 (Polychromatic418967fa.accept_7_1_5_3_1_268
  43 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 159 276 3 14 53 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 159 276
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 41 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 276 (Polychromatic418967fa.accept_14_12_5_10_1_2130 40 159 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 159 276 3 13 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 159 276
  (Polychromatic418967fa.accept_21_17_12_3_1_4848 38 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 159 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 159 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 159 276 3 12 53 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 159 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 276 (Polychromatic418967fa.accept_15_4_9_6_1_627 34 159 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 159 276 3 11 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 159 276
  (Polychromatic418967fa.accept_21_11_12_3_1_6461 32 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 159 276 (Polychromatic418967fa.accept_15_1_9_6_1_1323 31 159 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 159 276 3 10 53 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 159 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 276 (Polychromatic418967fa.accept_11_6_5_1_1_586 28 159 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 159 276 3 9 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159 276
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 26 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 159 276 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 159 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 159 276 3 8 53 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 159 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 159 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 276 3 7 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 276 (Polychromatic418967fa.accept_19_1_7_10_1_8926
  20 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 19 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 159 276 3 6 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 159 276 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 159 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 159 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 159 276 3 5 53 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 276
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 276 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 159 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 276 3 4 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 11
  159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 276
  (Polychromatic418967fa.accept_17_10_6_4_1_2506 10 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 159 276 3 3 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 159 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 159 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 276 (Polychromatic418967fa.accept_21_7_12_3_1_4849 7 159
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 276 3 2 53 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 276
  (Polychromatic418967fa.accept_10_5_9_6_1_697 5 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 276 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 159 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 276 3 1 53 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 159 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 159 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 159
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 158 276 (Eq.refl Bool.true) (allA_succ_of_gcd 118 158 276 2 59 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 158 276
  (Polychromatic418967fa.accept_18_9_14_6_1_1790 117 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 158 276 2 58 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 158 276 (accept_3_4 115 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 158 276 2 57 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 158 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 113 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 158 276 2 56 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 158 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 111 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 158 276 2 55 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 158 276 (accept_3_4 109 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 158 276 2 54 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 158 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 107 158 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 158 276 2 53 79 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 158 276
  (Polychromatic418967fa.accept_13_1_2_3_1_911 105 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 158 276 2 52 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 158 276 (accept_3_4 103 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 158 276 2 51 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 158 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 101 158 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 158 276 2 50 79 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 158 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 99 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 158 276 2 49 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 158 276 (accept_3_4 97 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 158 276 2 48 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 158 276 (Polychromatic418967fa.accept_16_15_14_4_1_6649 95 158 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 158 276 2 47 79 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 158 276
  (Polychromatic418967fa.accept_9_3_5_6_1_253 93 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 158 276 2 46 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 158 276 (accept_3_4 91 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 158 276 2 45 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 158 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 89 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 158 276 2 44 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 158 276
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 87 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 158 276 2 43 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 158 276 (accept_3_4 85 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 158 276 2 42 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 158 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 83 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 158 276 2 41 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 158 276
  (Polychromatic418967fa.accept_16_1_14_4_1_3220 81 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 158 276 2 40 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 158 276 (accept_3_4 79 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 158 276 2 39 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 158 276 (Polychromatic418967fa.accept_13_12_2_3_1_1527 77 158 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 158 276 2 38 79 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 158 276
  (Polychromatic418967fa.accept_9_3_5_6_1_253 75 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 158 276 2 37 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 158 276 (accept_3_4 73 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 158 276 2 36 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 158 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 158 276 2 35 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 158 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 158 276 2 34 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 158 276 (accept_3_4 67 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 158 276 2 33 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 158 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 65 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 158 276 2 32 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 158 276
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 158 276 2 31 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 158 276 (accept_3_4 61 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 158 276 2 30 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 276 (Polychromatic418967fa.accept_15_14_8_6_1_2133 59 158 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 276 2 29 79 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 158 276 2 28 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 158 276 (accept_3_4 55 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 276 2 27 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 276 2 26 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 276
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 51 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 276 2 25 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 276 (accept_3_4 49 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 276 2 24 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 276 2 23 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 276
  (Polychromatic418967fa.accept_18_9_14_6_1_1790 45 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 276 2 22 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 276 (accept_3_4 43 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 276 2 21 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 276 2 20 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 276
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 276 2 19 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 276 (accept_3_4 37 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 276 2 18 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 276 2 17 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 276
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 276 2 16 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 276 (accept_3_4 31 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 276 2 15 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 276 2 14 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 276 2 13 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 276 (accept_3_4 25 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 276 2 12 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 276 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 276 2 11 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 276
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 276 2 10 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 276 (accept_3_4 19 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 276 2 9 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 276 2 8 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 276 2 7 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 276 (accept_3_4 13 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 276 2 6 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 158 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 276 2 5 79 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 276
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 276 2 4 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 276 (accept_3_4 7 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  276 2 3 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 276 (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 158 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 276 2 2 79 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 158 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 276 2 1 79 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 276 (accept_3_4 1 158 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 120 157 276 (Eq.refl Bool.true) (allA_succ_of_accept 119 157 276 (accept_3_5 119 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 157 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 118 157 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 157 276
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 117 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 157 276 (accept_3_5 116 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 157 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 115 157 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 157 276 (Polychromatic418967fa.accept_21_9_10_3_1_262 114 157
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 157 276 (accept_3_5 113 157
  276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 157 276
  (Polychromatic418967fa.accept_11_2_3_1_1_244 112 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 157 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 111 157 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 157 276 (accept_3_5 110 157 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 157 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 109 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 157 276
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 108 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 157 276 (accept_3_5 107 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 157 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 106 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 157 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 105 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 157 276 (accept_3_5 104 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 157 276 (Polychromatic418967fa.accept_10_3_7_6_1_659 103 157
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 157 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 102 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 157 276 (accept_3_5 101 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 157 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 100 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 157 276 (Polychromatic418967fa.accept_18_9_13_6_1_877 99 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 157 276 (accept_3_5 98 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 157 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 97 157 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 157 276
  (Polychromatic418967fa.accept_13_5_1_3_1_878 96 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 157 276 (accept_3_5 95 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 157 276 (Polychromatic418967fa.accept_19_18_5_10_1_2175 94 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 157 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 93 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 157 276 (accept_3_5 92 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 157 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 91 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 157 276
  (Polychromatic418967fa.accept_11_2_3_1_1_244 90 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 157 276 (accept_3_5 89 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 157 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 88 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 157 276 (Polychromatic418967fa.accept_15_12_7_6_1_4013 87 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 157 276 (accept_3_5 86 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 157 276 (Polychromatic418967fa.accept_13_7_1_3_1_1523 85 157
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 157 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 84 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 157 276 (accept_3_5 83 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 157 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 82 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 157 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 157 276 (accept_3_5 80 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 157 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 79 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 157 276
  (Polychromatic418967fa.accept_19_2_5_10_1_4608 78 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 157 276 (accept_3_5 77 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 157 276 (Polychromatic418967fa.accept_13_11_1_3_1_910 76 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 157 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 75 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 157 276 (accept_3_5 74 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 157 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 73 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 157 276
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 72 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 157 276 (accept_3_5 71 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 157 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 157 276 (Polychromatic418967fa.accept_13_4_1_3_1_3058 69 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 276 (accept_3_5 68 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 157 276 (Polychromatic418967fa.accept_13_2_1_3_1_419 67 157
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 157 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 66 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 157 276 (accept_3_5 65 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 157 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 157 276 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 276 (accept_3_5 62 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 157 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 157 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 157 276
  (Polychromatic418967fa.accept_16_12_13_4_1_3198 60 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 157 276 (accept_3_5 59 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 157 276 (Polychromatic418967fa.accept_13_6_1_3_1_1522 58 157 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 157 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 157 276 (accept_3_5 56 157 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 157 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 55
  157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 157 276
  (Polychromatic418967fa.accept_13_2_1_3_1_419 54 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 157 276 (accept_3_5 53 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 157 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 157 276 (Polychromatic418967fa.accept_10_1_7_6_1_91 51 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 276 (accept_3_5 50 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 157 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 157 276 (accept_3_5 47 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 157 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 157 276 (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 276 (accept_3_5 44 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 157 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 276
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 42 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 157 276 (accept_3_5 41 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 157 276 (Polychromatic418967fa.accept_16_8_13_4_1_3258 40 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 157 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 276 (accept_3_5 38 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 276
  (Polychromatic418967fa.accept_21_15_10_3_1_9578 36 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 157 276 (accept_3_5 35 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 157 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 157 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 157 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 276 (accept_3_5 32 157 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 276 (Polychromatic418967fa.accept_10_1_7_6_1_91
  31 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 157 276 (accept_3_5 29 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 157 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 157 276 (Polychromatic418967fa.accept_14_13_3_10_1_2159 27 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 276 (accept_3_5 26 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 157 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 276
  (Polychromatic418967fa.accept_11_2_3_1_1_244 24 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 157 276 (accept_3_5 23 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 157 276 (Polychromatic418967fa.accept_16_6_13_4_1_643 22 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 157 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 276 (accept_3_5 20 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 276
  (Polychromatic418967fa.accept_13_5_1_3_1_878 18 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 276 (accept_3_5 17 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 276 (Polychromatic418967fa.accept_13_2_1_3_1_419 15 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 276 (accept_3_5 14 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 276 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 157
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 276
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 276 (accept_3_5 11 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 276 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 276 (accept_3_5 8 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 276
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 6 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 276 (accept_3_5 5 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 276 (Polychromatic418967fa.accept_13_4_1_3_1_3058 4 157 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 276 (accept_3_5 2 157 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 157 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 121 156 276 (Eq.refl Bool.true) (allA_succ_of_gcd 120 156 276 12 10 13 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 156 276
  (Polychromatic418967fa.accept_9_2_3_6_1_88 119 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 156 276 2 59 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 117 156 276 3 39 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 116 156 276 4 29 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 156 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 115 156
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 156 276 6 19 26 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 156 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 113 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 156 276 4 28 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 156 276 3 37 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 156 276 2 55 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 156 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 109 156 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 156 276 12 9 13 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 156 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 107 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 156 276 2 53 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 105 156 276 3 35 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 104 156 276 4 26 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 156 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 103 156
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 156 276 6 17 26 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 156 276
  (Polychromatic418967fa.accept_9_2_3_6_1_88 101 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 156 276 4 25 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 99 156 276 3 33 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 156 276 2 49 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 156 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 156 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 156 276 12 8 13 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 156 276
  (Polychromatic418967fa.accept_9_5_3_6_1_269 95 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 156 276 2 47 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 156 276 3 31 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 156 276 4 23 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 156 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 91 156 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 156 276 6 15 26 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 156 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 89 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 156 276 4 22 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 156 276 3 29 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 156 276 2 43 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 156 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 156 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 156 276 12 7 13 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 156 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 83 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 156 276 2 41 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 156 276 3 27 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 156 276 4 20 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 156 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 156 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 156 276 6 13 26 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 156 276
  (Polychromatic418967fa.accept_9_5_3_6_1_269 77 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 156 276 4 19 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 156 276 3 25 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 156 276 2 37 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 156 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 156 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 156 276 12 6 13 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 156 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 156 276 2 35 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 156 276 3 23 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 156 276 4 17 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 276 (Polychromatic418967fa.accept_9_4_3_6_1_532 67 156 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 156 276 6 11 26 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 156 276
  (Polychromatic418967fa.accept_9_2_3_6_1_88 65 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 156 276 4 16 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 156 276 3 21 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 156 276 2 31 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 156 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 156 276 12 5 13 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 156 276
  (Polychromatic418967fa.accept_9_5_3_6_1_269 59 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 156 276 2 29 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 156 276 3 19 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 156 276 4 14 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 156 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 156 276 6 9 26 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 156 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 156 276 4 13 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 156 276 3 17 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 156 276 2 25 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 276 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 156 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 156 276 12 4 13 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 156 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 156 276 2 23 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 156 276 3 15 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 156 276 4 11 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 156 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 156 276 6 7 26 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 156 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 156 276 4 10 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 156 276 3 13 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 156 276 2 19 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 156 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 156 276 12 3 13 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 156 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 156 276 2 17 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 156 276 3 11 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 156 276 4 8 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 156 276 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 156 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 276 6 5 26 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 156 276 4 7 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 156 276 3 9 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 156 276 2 13 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 156 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 156 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 276 12 2 13 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 276
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 156 276 2 11 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 156 276 3 7 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 156 276 4 5 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 156 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 156 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 276 6 3 26 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 276 4 4 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 156 276 3 5 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 156 276 2 7 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 156 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 156 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 276 12 1 13 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 276
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 276 2 5 78 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 156 276 3 3 52 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 156 276 4 2 39 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 156 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 156 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 276 6 1 26 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 5
  156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 276 4 1 39 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 276 3 1 52 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 276 2 1 78 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 156 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 155 276 (Eq.refl Bool.true) (allA_succ_of_accept 121 155 276 (accept_3_4 121 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 155 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 120 155
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 155 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 119 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 155 276 (accept_3_4 118 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 155 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 117 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 155 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 116 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 155 276 (accept_3_4 115 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 155 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 114 155
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 155 276
  (Polychromatic418967fa.accept_9_5_2_6_1_265 113 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 155 276 (accept_3_4 112 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 155 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 111 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 155 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 110 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 155 276 (accept_3_4 109 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 155 276 (Polychromatic418967fa.accept_13_4_12_3_1_2999 108
  155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 155 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 107 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 155 276 (accept_3_4 106 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 155 276 (Polychromatic418967fa.accept_16_9_11_4_1_3194 105 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 155 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 104 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 155 276 (accept_3_4 103 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 155 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 102 155
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 155 276
  (Polychromatic418967fa.accept_10_1_5_6_1_649 101 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 155 276 (accept_3_4 100 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 155 276 (Polychromatic418967fa.accept_10_9_5_6_1_691 99 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 155 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 98 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 155 276 (accept_3_4 97 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 155 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 155 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 95 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 155 276 (accept_3_4 94 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 155 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 93 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 155 276 (Polychromatic418967fa.accept_16_12_11_4_1_1359 92 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 155 276 (accept_3_4 91 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 155 276 (Polychromatic418967fa.accept_20_10_15_16_1_6994 90
  155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 155 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 89 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 155 276 (accept_3_4 88 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 155 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 155 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 86 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 155 276 (accept_3_4 85 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 155 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 155 276
  (Polychromatic418967fa.accept_17_15_2_4_1_2423 83 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 155 276 (accept_3_4 82 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 155 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 155 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 80 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 155 276 (accept_3_4 79 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 155 276 (Polychromatic418967fa.accept_15_3_5_6_1_4005 78 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 155 276
  (Polychromatic418967fa.accept_9_5_2_6_1_265 77 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 155 276 (accept_3_4 76 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 155 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 155 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 74 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 155 276 (accept_3_4 73 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 155 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 71 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 155 276 (accept_3_4 70 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 155 276 (Polychromatic418967fa.accept_10_9_5_6_1_691 69 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 155 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 276 (accept_3_4 67 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 155 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 155 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 155 276 (accept_3_4 64 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 155 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 155 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 62 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 276 (accept_3_4 61 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 276
  (Polychromatic418967fa.accept_9_5_2_6_1_265 59 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 155 276 (accept_3_4 58 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 155 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 155 276 (Polychromatic418967fa.accept_13_4_12_3_1_2999 56 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 276 (accept_3_4 55 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 155 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 276 (accept_3_4 52 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 155 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 50 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 276 (accept_3_4 49 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 276 (accept_3_4 46 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 276 (Polychromatic418967fa.accept_19_7_3_10_1_4674 45 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 276 (accept_3_4 43 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 276 (Polychromatic418967fa.accept_15_12_5_6_1_2148 42 155 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 276
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 155 276 (accept_3_4 40 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 155 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 155 276 (Polychromatic418967fa.accept_16_6_11_4_1_635 38 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 276 (accept_3_4 37 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 276 (Polychromatic418967fa.accept_21_15_8_3_1_8086 36 155
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 276
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 276 (accept_3_4 34 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 276 (accept_3_4 31 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 276
  (Polychromatic418967fa.accept_10_9_5_6_1_691 29 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 276 (accept_3_4 28 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 276 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 276 (accept_3_4 25 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 276 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 276 (accept_3_4 22 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 276 (Polychromatic418967fa.accept_19_1_3_10_1_8917 20 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 276 (accept_3_4 19 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 155 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 276
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 276 (accept_3_4 16 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 276 (accept_3_4 13 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 276 (accept_3_4 10 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 276 (accept_3_4 7 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 276 (Polychromatic418967fa.accept_16_6_11_4_1_635 6 155 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 276 (accept_3_4 4 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 155 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 276 (accept_3_4 1 155 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 123 154 276 (Eq.refl Bool.true) (allA_succ_of_gcd 122 154 276 2 61 77 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 154 276
  (Polychromatic418967fa.accept_9_4_1_6_1_284 121 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 154 276 2 60 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 154 276 (accept_3_5 119 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 154 276 2 59 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 154 276 (Polychromatic418967fa.accept_21_12_7_3_1_4927 117 154 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 154 276 2 58 77 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 154 276
  (Polychromatic418967fa.accept_9_7_1_6_1_261 115 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 154 276 2 57 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 154 276 (accept_3_5 113 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 154 276 2 56 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 154 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 111 154 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 154 276 2 55 77 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 154 276
  (Polychromatic418967fa.accept_13_5_11_3_1_902 109 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 154 276 2 54 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 154 276 (accept_3_5 107 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 154 276 2 53 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 154 276 (Polychromatic418967fa.accept_10_5_4_6_1_319 105 154 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 154 276 2 52 77 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 154 276
  (Polychromatic418967fa.accept_9_4_1_6_1_284 103 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 154 276 2 51 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 154 276 (accept_3_5 101 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 154 276 2 50 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 154 276 (Polychromatic418967fa.accept_13_8_11_3_1_3053 99 154 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 154 276 2 49 77 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 154 276
  (Polychromatic418967fa.accept_9_7_1_6_1_261 97 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 154 276 2 48 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 154 276 (accept_3_5 95 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 154 276 2 47 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 154 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 93 154 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 154 276 2 46 77 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 154 276
  (Polychromatic418967fa.accept_25_16_4_1_1_6245 91 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 154 276 2 45 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 154 276 (accept_3_5 89 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 154 276 2 44 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 154 276 (Polychromatic418967fa.accept_18_15_10_6_1_1781 87 154 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 154 276 2 43 77 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 154 276
  (Polychromatic418967fa.accept_9_4_1_6_1_284 85 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 154 276 2 42 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 154 276 (accept_3_5 83 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 154 276 2 41 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 154 276 (Polychromatic418967fa.accept_19_5_2_10_1_3371 81 154 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 154 276 2 40 77 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 154 276
  (Polychromatic418967fa.accept_9_7_1_6_1_261 79 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 154 276 2 39 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 154 276 (accept_3_5 77 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 154 276 2 38 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 154 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 75 154 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 154 276 2 37 77 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 154 276
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 73 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 154 276 2 36 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 154 276 (accept_3_5 71 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 154 276 2 35 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 154 276 (Polychromatic418967fa.accept_15_9_4_6_1_3075 69 154 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 154 276 2 34 77 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 154 276
  (Polychromatic418967fa.accept_9_4_1_6_1_284 67 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 154 276 2 33 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 154 276 (accept_3_5 65 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 154 276 2 32 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 154 276 (Polychromatic418967fa.accept_19_6_2_10_1_4691 63 154 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 154 276 2 31 77 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 154 276
  (Polychromatic418967fa.accept_9_7_1_6_1_261 61 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 154 276 2 30 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 154 276 (accept_3_5 59 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 154 276 2 29 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 154 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 154 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 276 2 28 77 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 154 276
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 154 276 2 27 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 154 276 (accept_3_5 53 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 154 276 2 26 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 154 276 (Polychromatic418967fa.accept_18_15_10_6_1_1781 51 154 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 154 276 2 25 77 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 154 276
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 154 276 2 24 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 154 276 (accept_3_5 47 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 154 276 2 23 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 154 276 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 154 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 276 2 22 77 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 276
  (Polychromatic418967fa.accept_9_7_1_6_1_261 43 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 154 276 2 21 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 154 276 (accept_3_5 41 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 276 2 20 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 154 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 276 2 19 77 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 276
  (Polychromatic418967fa.accept_19_18_2_10_1_10412 37 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 154 276 2 18 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 154 276 (accept_3_5 35 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 154 276 2 17 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 154 276 (Polychromatic418967fa.accept_13_7_11_3_1_1540 33 154 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 276 2 16 77 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 276
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 276 2 15 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 276 (accept_3_5 29 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 276 2 14 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 276 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 154 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 276 2 13 77 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 276
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 276 2 12 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 276 (accept_3_5 23 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 276 2 11 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 154 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 276 2 10 77 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 276
  (Polychromatic418967fa.accept_25_19_4_1_1_13521 19 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 154 276 2 9 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 154 276 (accept_3_5 17 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 276 2 8 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 154 276 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 154 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 276 2 7 77 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 276
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 154 276 2 6 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 154 276 (accept_3_5 11 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 276 2 5 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 154 276 (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 154 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 276 2 4 77 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 276
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 276 2 3 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 276 (accept_3_5 5 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  276 2 2 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 154 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 276 2 1 77 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 276 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 154 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 124 153 276 (Eq.refl Bool.true) (allA_succ_of_gcd 123 153 276 3 41 51 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 153 276
  (Polychromatic418967fa.accept_18_14_9_6_1_1777 122 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 121 153 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 121 153 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 153 276 3 40 51 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 153 276
  (Polychromatic418967fa.accept_10_9_3_6_1_686 119 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 153 276 (Polychromatic418967fa.accept_10_8_3_6_1_685 118 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 117 153 276 3 39 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 116 153 276 (Polychromatic418967fa.accept_7_4_6_3_1_271
  116 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 153 276
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 115 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 153 276 3 38 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 153 276 (Polychromatic418967fa.accept_21_8_6_3_1_4881 113 153 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 153 276
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 112 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 111 153 276 3 37 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 110 153 276 (Polychromatic418967fa.accept_13_6_10_3_1_897 110 153 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 153 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 109 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 153 276 3 36 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 153 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 107 153 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 153 276
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 106 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 153 276 3 35 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 153 276 (Polychromatic418967fa.accept_16_8_9_4_1_630 104 153 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 153 276
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 103 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 153 276 3 34 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 153 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 101 153 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 153 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 100 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 99 153 276 3 33 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 98 153 276 (Polychromatic418967fa.accept_10_8_3_6_1_685 98 153 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 153 276 (Polychromatic418967fa.accept_10_7_3_6_1_644
  97 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 153 276 3 32 51 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 153 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 95 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 153 276 (Polychromatic418967fa.accept_16_14_9_4_1_6693 94 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 153 276 3 31 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 153 276 (Polychromatic418967fa.accept_16_12_9_4_1_4345
  92 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 153 276
  (Polychromatic418967fa.accept_15_1_3_6_1_621 91 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 153 276 3 30 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 153 276 (Polychromatic418967fa.accept_10_9_3_6_1_686 89 153 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 153 276 (Polychromatic418967fa.accept_7_4_6_3_1_271
  88 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 153 276 3 29 51 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 153 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 86 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 153 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 85 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 153 276 3 28 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 153 276 (Polychromatic418967fa.accept_19_7_1_10_1_4702
  83 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 276
  (Polychromatic418967fa.accept_19_6_1_10_1_7449 82 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 153 276 3 27 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 153 276 (Polychromatic418967fa.accept_13_2_10_3_1_1538 80 153 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 153 276 3 26 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 153 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 77 153 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 276
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 76 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 153 276 3 25 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 153 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 153 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 153 276
  (Polychromatic418967fa.accept_14_3_13_10_1_761 73 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 153 276 3 24 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 153 276 (Polychromatic418967fa.accept_13_6_10_3_1_897 71 153 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 276
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 70 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 153 276 3 23 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 153 276 (Polychromatic418967fa.accept_10_8_3_6_1_685 68 153 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 276 (Polychromatic418967fa.accept_7_4_6_3_1_271
  67 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 153 276 3 22 51 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 153 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 153 276 (Polychromatic418967fa.accept_11_9_10_1_1_581 64 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 153 276 3 21 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 153 276 (Polychromatic418967fa.accept_16_14_9_4_1_6693
  62 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 61 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 153 276 3 20 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 153 276 (Polychromatic418967fa.accept_10_9_3_6_1_686 59 153 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 276 (Polychromatic418967fa.accept_7_2_6_3_1_100
  58 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 153 276 3 19 51 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 153 276
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 56 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 276 (Polychromatic418967fa.accept_15_10_3_6_1_3042 55 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 153 276 3 18 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 153 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 53
  153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 276
  (Polychromatic418967fa.accept_19_14_1_10_1_11713 52 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 153 276 3 17 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 153 276 (Polychromatic418967fa.accept_13_11_10_3_1_3020 50 153 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 276
  (Polychromatic418967fa.accept_10_9_3_6_1_686 49 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 153 276 3 16 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 153 276 (Polychromatic418967fa.accept_10_7_3_6_1_644 47 153 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 276 (Polychromatic418967fa.accept_7_4_6_3_1_271
  46 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 153 276 3 15 51 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 153 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 276 (Polychromatic418967fa.accept_16_11_9_4_1_5438 43 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 153 276 3 14 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 153 276 (Polychromatic418967fa.accept_13_2_10_3_1_1538
  41 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 276
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 40 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 153 276 3 13 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 153 276 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 153 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 276 (Polychromatic418967fa.accept_7_2_6_3_1_100
  37 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 153 276 3 12 51 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 153 276
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 276 (Polychromatic418967fa.accept_21_13_6_3_1_3381 34 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 153 276 3 11 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 153 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 32
  153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 276
  (Polychromatic418967fa.accept_11_9_10_1_1_581 31 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 153 276 3 10 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 153 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 153 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 276 (Polychromatic418967fa.accept_10_8_3_6_1_685
  28 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 153 276 3 9 51 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153 276
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 153 276 3 8 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 153 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 276
  (Polychromatic418967fa.accept_19_3_1_10_1_2193 22 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 153 276 3 7 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 153 276 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 276 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 153
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 276 3 6 51 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 276
  (Polychromatic418967fa.accept_10_7_3_6_1_644 17 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 276 3 5 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 276 (Polychromatic418967fa.accept_16_14_9_4_1_6693
  14 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 13 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 153 276 3 4 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 153 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 276 (Polychromatic418967fa.accept_15_10_3_6_1_3042 10 153
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 276 3 3 51 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 276
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 276 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 276 3 2 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 153 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 153 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 153 276 3 1 51 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 153 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 153 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 276 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 153 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 152 276 (Eq.refl Bool.true) (allA_succ_of_gcd 124 152 276 4 31 38 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 152 276
  (Polychromatic418967fa.accept_13_6_9_3_1_915 123 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 152 276 2 61 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 152 276 (accept_3_4 121 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 152 276 4 30 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 152 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 119 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 152 276 2 59 76 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 152 276
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 117 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 152 276 4 29 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 152 276 (accept_3_4 115 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 152 276 2 57 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 152 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 113 152 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 152 276 4 28 38 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 152 276
  (Polychromatic418967fa.accept_9_3_8_6_1_80 111 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 152 276 2 55 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 152 276 (accept_3_4 109 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 152 276 4 27 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 152 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 107 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 152 276 2 53 76 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 152 276
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 105 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 152 276 4 26 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 152 276 (accept_3_4 103 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 152 276 2 51 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 152 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 101 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 152 276 4 25 38 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 152 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 99 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 152 276 2 49 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 152 276 (accept_3_4 97 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 152 276 4 24 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 152 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 95 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 152 276 2 47 76 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 152 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 93 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 152 276 4 23 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 152 276 (accept_3_4 91 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 152 276 2 45 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 152 276 (Polychromatic418967fa.accept_14_5_12_10_1_2985 89 152 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 152 276 4 22 38 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 152 276
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 87 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 152 276 2 43 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 152 276 (accept_3_4 85 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 152 276 4 21 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 152 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 83 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 152 276 2 41 76 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 152 276
  (Polychromatic418967fa.accept_10_1_2_6_1_638 81 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 152 276 4 20 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 152 276 (accept_3_4 79 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 152 276 2 39 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 152 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 77 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 152 276 4 19 38 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 152 276
  (Polychromatic418967fa.accept_9_3_8_6_1_80 75 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 152 276 2 37 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 152 276 (accept_3_4 73 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 152 276 4 18 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 152 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 276 2 35 76 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 276
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 69 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 152 276 4 17 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 152 276 (accept_3_4 67 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 152 276 2 33 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 276 4 16 38 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 276
  (Polychromatic418967fa.accept_16_15_8_4_1_1355 63 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 276 2 31 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 276 (accept_3_4 61 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 276 4 15 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 59 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 276 2 29 76 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 276 4 14 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 152 276 (accept_3_4 55 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 152 276 2 27 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 152 276 (Polychromatic418967fa.accept_15_8_2_6_1_2125 53 152 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 276 4 13 38 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 276 2 25 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 276 (accept_3_4 49 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 276 4 12 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 276 2 23 76 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 276
  (Polychromatic418967fa.accept_13_6_9_3_1_915 45 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 276 4 11 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 276 (accept_3_4 43 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 276 2 21 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 276 4 10 38 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 276
  (Polychromatic418967fa.accept_9_3_8_6_1_80 39 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 276 2 19 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 276 (accept_3_4 37 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 276 4 9 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 152 276 (Polychromatic418967fa.accept_16_3_8_4_1_3279 35 152 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 276 2 17 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 276 (Polychromatic418967fa.accept_13_7_9_3_1_1504
  33 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 152 276 4 8 38 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 152 276
  (accept_3_4 31 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 152 276 2 15 76 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 152 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 152 276 4 7 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 152 276 (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 152 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 152 276 2 13 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 152 276 (accept_3_4 25 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 152 276 4 6 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 152 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 152 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 276 2 11 76 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 276
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 276 4 5 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 152 276 (accept_3_4 19 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  152 276 2 9 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 152 276 (Polychromatic418967fa.accept_16_1_8_4_1_4334 17 152 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 276 4 4 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 15
  152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 276 2 7 76 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 276 (accept_3_4 13
  152 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 276 4 3 38 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 276
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 152 276 2 5 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 152 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 276 4 2 38 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 276 (accept_3_4 7 152 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152 276 2 3 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 152 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 152 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 276 4 1 38 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 276
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 152 276 2 1 76 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 152 276 (accept_3_4 1 152 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 126 151 276 (Eq.refl Bool.true) (allA_succ_of_accept 125 151 276 (accept_3_5 125 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 151 276 (Polychromatic418967fa.accept_13_7_8_3_1_1533 124 151
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 151 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 123 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 151 276 (accept_3_5 122 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 151 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 121 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 151 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 120 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 151 276 (accept_3_5 119 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 151 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 118 151
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 151 276
  (Polychromatic418967fa.accept_10_7_1_6_1_673 117 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 151 276 (accept_3_5 116 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 151 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 115 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 151 276 (Polychromatic418967fa.accept_11_4_8_1_1_1047 114 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 151 276 (accept_3_5 113 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 151 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 112 151
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 151 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 111 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 151 276 (accept_3_5 110 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 151 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 109 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 151 276 (Polychromatic418967fa.accept_15_3_1_6_1_206 108 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 151 276 (accept_3_5 107 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 151 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 106 151
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 151 276
  (Polychromatic418967fa.accept_10_5_1_6_1_672 105 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 151 276 (accept_3_5 104 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 151 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 103 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 151 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 102 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 151 276 (accept_3_5 101 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 151 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 100 151
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 151 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 99 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 151 276 (accept_3_5 98 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 151 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 151 276 (Polychromatic418967fa.accept_13_5_8_3_1_1535 96 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 151 276 (accept_3_5 95 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 151 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 94 151 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 151 276
  (Polychromatic418967fa.accept_9_3_7_6_1_76 93 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 151 276 (accept_3_5 92 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 151 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 91 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 151 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 151 276 (accept_3_5 89 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 151 276 (Polychromatic418967fa.accept_16_8_7_4_1_2217 88 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 151 276
  (Polychromatic418967fa.accept_10_7_1_6_1_673 87 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 151 276 (accept_3_5 86 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 151 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 151 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 84 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 151 276 (accept_3_5 83 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 151 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 82 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 151 276
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 151 276 (accept_3_5 80 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 151 276 (Polychromatic418967fa.accept_17_11_15_4_1_2415 79 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 151 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 151 276 (accept_3_5 77 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 151 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 75 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 151 276 (accept_3_5 74 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 151 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 151 276 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 276 (accept_3_5 71 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 276 (Polychromatic418967fa.accept_11_4_8_1_1_1047 70 151
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 151 276 (accept_3_5 68 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 151 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 151 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 66 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 276 (accept_3_5 65 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 276
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 63 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 276 (accept_3_5 62 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 276 (Polychromatic418967fa.accept_13_9_8_3_1_3045 61 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 276 (Polychromatic418967fa.accept_16_12_7_4_1_687 60 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 276 (accept_3_5 59 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 151 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 276 (accept_3_5 56 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 276 (Polychromatic418967fa.accept_15_9_1_6_1_657 54 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 276 (accept_3_5 53 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 276 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 151
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 51 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 276 (accept_3_5 50 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 276 (accept_3_5 47 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 276
  (Polychromatic418967fa.accept_10_5_1_6_1_672 45 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 276 (accept_3_5 44 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 276 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 276 (accept_3_5 41 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 151 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 276
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 276 (accept_3_5 38 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 276 (accept_3_5 35 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 276
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 33 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 276 (accept_3_5 32 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 276 (accept_3_5 29 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 276 (accept_3_5 26 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 276 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 276 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 276 (accept_3_5 23 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 151 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 276
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 276 (accept_3_5 20 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 276 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 276 (accept_3_5 17 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 276 (Polychromatic418967fa.accept_17_16_15_4_1_8559 16 151
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 276 (accept_3_5 14 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 276 (accept_3_5 11 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 276 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 276
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 276 (accept_3_5 8 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 276 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 276 (accept_3_5 5 151 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 276 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 151 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 276 (accept_3_5 2 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 151 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 127 150 276 (Eq.refl Bool.true) (allA_succ_of_gcd 126 150 276 6 21 25 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 150 276
  (Polychromatic418967fa.accept_13_8_7_3_1_430 125 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 150 276 2 62 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 123 150 276 3 41 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 122 150 276 2 61 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 150 276 (Polychromatic418967fa.accept_13_4_7_3_1_92 121 150
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 150 276 6 20 25 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 150 276
  (Polychromatic418967fa.accept_20_19_10_16_1_7001 119 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 118 150 276 2 59 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 117 150 276 3 39 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 116 150 276 2 58 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 150 276 (Polychromatic418967fa.accept_13_11_7_3_1_894
  115 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 150 276 6 19 25 46
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 150 276
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 113 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 150 276 2 56 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 150 276 3 37 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 150 276 2 55 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 150 276 (Polychromatic418967fa.accept_16_13_6_4_1_3277 109 150
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 150 276 6 18 25 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 150 276
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 107 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 150 276 2 53 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 105 150 276 3 35 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 150 276 2 52 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 150 276
  (Polychromatic418967fa.accept_17_1_14_4_1_1550 103 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 150 276 6 17 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 150 276 (Polychromatic418967fa.accept_13_10_7_3_1_3041 101 150 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 150 276 2 50 75 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 99 150 276 3 33 50 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 150 276 2 49 75
  138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 150 276
  (Polychromatic418967fa.accept_19_2_17_10_1_4629 97 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 150 276 6 16 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 150 276 (Polychromatic418967fa.accept_13_4_7_3_1_92 95 150 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 150 276 2 47 75 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 150 276 3 31 50 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 150 276 2 46 75 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 150 276
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 91 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 150 276 6 15 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 150 276 (Polychromatic418967fa.accept_13_11_7_3_1_894 89 150 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 150 276 2 44 75 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 150 276 3 29 50 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 150 276 2 43 75 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 150 276
  (Polychromatic418967fa.accept_16_5_6_4_1_3211 85 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 150 276 6 14 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 150 276 (Polychromatic418967fa.accept_11_6_7_1_1_564 83 150 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 150 276 2 41 75 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 150 276 3 27 50 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 150 276 2 40 75 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 150 276
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 79 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 276 6 13 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 276 (Polychromatic418967fa.accept_16_13_6_4_1_3277 77 150 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 150 276 2 38 75 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 150 276 3 25 50 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 150 276 2 37 75 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 276
  (Polychromatic418967fa.accept_13_8_7_3_1_430 73 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 276 6 12 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 276 (Polychromatic418967fa.accept_22_5_18_12_1_7664 71 150 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 150 276 2 35 75 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 150 276 3 23 50 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 150 276 2 34 75 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 276
  (Polychromatic418967fa.accept_16_3_6_4_1_679 67 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 276 6 11 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 276 (Polychromatic418967fa.accept_19_8_17_10_1_8900 65 150 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 150 276 2 32 75 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 150 276 3 21 50 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 150 276 2 31 75 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 276
  (Polychromatic418967fa.accept_11_6_7_1_1_564 61 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 276 6 10 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 276 (Polychromatic418967fa.accept_16_11_6_4_1_2228 59 150 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 276 2 29 75 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 150 276 3 19 50 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 150 276 2 28 75 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 276
  (Polychromatic418967fa.accept_20_15_10_16_1_8506 55 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 150 276 6 9 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 150 276 (Polychromatic418967fa.accept_13_1_7_3_1_1503 53 150 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 276 2 26 75 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 150 276 3 17 50 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 150 276 2 25 75 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 276
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 49 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 276 6 8 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 150 276 (Polychromatic418967fa.accept_13_8_7_3_1_430 47 150 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 276 2 23 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 150 276 3 15 50 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 276 2 22 75 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 276
  (Polychromatic418967fa.accept_13_4_7_3_1_92 43 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 276 6 7 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 150 276 (Polychromatic418967fa.accept_17_7_14_4_1_4745 41 150 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 276 2 20 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 150 276 3 13 50 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 150 276 2 19 75 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 276
  (Polychromatic418967fa.accept_13_11_7_3_1_894 37 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 276 6 6 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 150 276 (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 150 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 276 2 17 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 150 276 3 11 50 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 150 276 2 16 75 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 276
  (Polychromatic418967fa.accept_19_12_17_10_1_7365 31 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 150 276 6 5 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 150 276 (Polychromatic418967fa.accept_16_13_6_4_1_3277 29 150 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 276 2 14 75 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 150 276 3 9 50 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 150 276 2 13 75 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 276
  (Polychromatic418967fa.accept_20_5_10_16_1_9890 25 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 150 276 6 4 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 150 276 (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 150 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 276 2 11 75 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 150 276 3 7 50 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 150 276 2 10 75 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 276
  (Polychromatic418967fa.accept_16_3_6_4_1_679 19 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 276 6 3 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 276 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 150 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 276 2 8 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 276 3 5 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 276 2 7 75 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 276
  (Polychromatic418967fa.accept_16_13_6_4_1_3277 13 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 276 6 2 25 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 150 276 (Polychromatic418967fa.accept_13_11_7_3_1_894 11 150 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 276 2 5 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 150 276 3 3 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 150 276 2 4 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 276 (Polychromatic418967fa.accept_17_7_14_4_1_4745
  7 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 276 6 1 25 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 276
  (Polychromatic418967fa.accept_16_5_6_4_1_3211 5 150 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 150 276 2 2 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 150 276 3 1 50 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 150 276 2 1 75 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 150 276 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 150 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 150
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 128 149 276 (Eq.refl Bool.true) (allA_succ_of_accept 127 149 276 (accept_3_4 127 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 149 276 (Polychromatic418967fa.accept_11_5_6_1_1_988 126 149
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 149 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 125 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 149 276 (accept_3_4 124 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 149 276 (Polychromatic418967fa.accept_10_3_9_6_1_94 123 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 149 276 (Polychromatic418967fa.accept_13_5_6_3_1_868 122 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 149 276 (accept_3_4 121 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 149 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 120 149
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 149 276
  (Polychromatic418967fa.accept_9_2_5_6_1_536 119 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 149 276 (accept_3_4 118 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 149 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 117 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 149 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 116 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 149 276 (accept_3_4 115 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 149 276 (Polychromatic418967fa.accept_13_10_6_3_1_1515 114
  149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 149 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 113 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 149 276 (accept_3_4 112 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 149 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 111 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 149 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 110 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 149 276 (accept_3_4 109 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 149 276 (Polychromatic418967fa.accept_16_12_5_4_1_3275 108
  149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 149 276
  (Polychromatic418967fa.accept_9_8_5_6_1_538 107 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 149 276 (accept_3_4 106 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 149 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 105 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 149 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 104 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 149 276 (accept_3_4 103 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 149 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 102 149
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 149 276
  (Polychromatic418967fa.accept_9_2_5_6_1_536 101 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 149 276 (accept_3_4 100 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 149 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 99 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 149 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 98 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 149 276 (accept_3_4 97 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 149 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 149 276
  (Polychromatic418967fa.accept_10_5_9_6_1_697 95 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 149 276 (accept_3_4 94 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 149 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 93 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 149 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 92 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 149 276 (accept_3_4 91 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 149 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 149 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 89 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 149 276 (accept_3_4 88 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 149 276 (Polychromatic418967fa.accept_13_9_6_3_1_1514 87 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 149 276 (Polychromatic418967fa.accept_16_6_5_4_1_4330 86 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 149 276 (accept_3_4 85 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 149 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 149 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 149 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 83 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 149 276 (accept_3_4 82 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 149 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 149 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 80 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 276 (accept_3_4 79 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 149 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 149 276
  (Polychromatic418967fa.accept_17_9_13_4_1_2408 77 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 149 276 (accept_3_4 76 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 149 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 149 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 74 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 276 (accept_3_4 73 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 276 (Polychromatic418967fa.accept_16_8_5_4_1_674 72 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 149 276 (accept_3_4 70 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 149 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 149 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 276 (accept_3_4 67 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 149 276
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 149 276 (accept_3_4 64 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 149 276 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 149 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 276 (accept_3_4 61 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 276 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 276
  (Polychromatic418967fa.accept_17_8_13_4_1_6012 59 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 149 276 (accept_3_4 58 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 149 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 149 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 56 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 276 (accept_3_4 55 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 149 276
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 149 276 (accept_3_4 52 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 149 276 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 149 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 276 (accept_3_4 49 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 149 276 (accept_3_4 46 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 149 276 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 149 276 (Polychromatic418967fa.accept_9_8_5_6_1_538 44 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 276 (accept_3_4 43 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 276 (Polychromatic418967fa.accept_17_8_13_4_1_6012 42 149 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 149 276 (accept_3_4 40 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 149 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 276 (accept_3_4 37 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 276
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 276 (accept_3_4 34 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 276 (Polychromatic418967fa.accept_19_13_16_10_1_6016 32 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 276 (accept_3_4 31 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 149 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 276 (accept_3_4 28 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 276 (accept_3_4 25 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 276 (Polychromatic418967fa.accept_15_9_14_6_1_3004 24 149 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 276
  (Polychromatic418967fa.accept_10_3_9_6_1_94 23 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 276 (accept_3_4 22 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 276 (accept_3_4 19 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 276 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 276
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 276 (accept_3_4 16 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 276 (Polychromatic418967fa.accept_13_1_6_3_1_1547 14 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 276 (accept_3_4 13 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 149 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 276
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 276 (accept_3_4 10 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 276 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 276 (accept_3_4 7 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 149 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 276 (accept_3_4 4 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 276 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 149 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 276 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 276 (accept_3_4 1 149 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 129 148 276 (Eq.refl Bool.true) (allA_succ_of_gcd 128 148 276 4 32 37 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 148 276
  (Polychromatic418967fa.accept_9_1_4_6_1_5 127 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 148 276 2 63 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 148 276 (accept_3_5 125 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 148 276 4 31 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 148 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 123 148 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 148 276 2 61 74 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 148 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 121 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 148 276 4 30 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 148 276 (accept_3_5 119 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 148 276 2 59 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 148 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 117 148 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 148 276 4 29 37 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 148 276
  (Polychromatic418967fa.accept_9_7_4_6_1_273 115 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 148 276 2 57 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 148 276 (accept_3_5 113 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 148 276 4 28 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 148 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 111 148 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 148 276 2 55 74 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 148 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 109 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 148 276 4 27 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 148 276 (accept_3_5 107 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 148 276 2 53 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 148 276 (Polychromatic418967fa.accept_11_6_5_1_1_586 105 148 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 148 276 4 26 37 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 148 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 103 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 148 276 2 51 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 148 276 (accept_3_5 101 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 148 276 4 25 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 148 276 (Polychromatic418967fa.accept_13_8_5_3_1_427 99 148 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 148 276 2 49 74 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 148 276
  (Polychromatic418967fa.accept_9_7_4_6_1_273 97 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 148 276 4 24 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 148 276 (accept_3_5 95 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 148 276 2 47 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 148 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 93 148 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 148 276 4 23 37 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 148 276
  (Polychromatic418967fa.accept_9_1_4_6_1_5 91 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 148 276 2 45 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 148 276 (accept_3_5 89 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 148 276 4 22 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 148 276 (Polychromatic418967fa.accept_13_9_5_3_1_428 87 148 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 148 276 2 43 74 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 148 276
  (Polychromatic418967fa.accept_19_9_15_10_1_7443 85 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 148 276 4 21 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 148 276 (accept_3_5 83 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 148 276 2 41 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 148 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 148 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 148 276 4 20 37 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 148 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 79 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 148 276 2 39 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 148 276 (accept_3_5 77 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 148 276 4 19 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 148 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 148 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 148 276 2 37 74 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 148 276
  (Polychromatic418967fa.accept_9_1_4_6_1_5 73 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 148 276 4 18 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 148 276 (accept_3_5 71 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 276 2 35 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 276 (Polychromatic418967fa.accept_18_15_4_6_1_1763 69 148 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 276 4 17 37 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 276
  (Polychromatic418967fa.accept_7_4_1_3_1_277 67 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 148 276 2 33 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 148 276 (accept_3_5 65 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 276 4 16 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 276 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 148 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 276 2 31 74 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 276 4 15 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 276 (accept_3_5 59 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 276 2 29 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 148 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 276 4 14 37 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 276
  (Polychromatic418967fa.accept_9_1_4_6_1_5 55 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 148 276 2 27 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 148 276 (accept_3_5 53 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 276 4 13 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 276 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 148 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 276 2 25 74 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 276
  (Polychromatic418967fa.accept_15_4_13_6_1_642 49 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 148 276 4 12 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 148 276 (accept_3_5 47 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 276 2 23 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 276 (Polychromatic418967fa.accept_13_6_5_3_1_426 45 148 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 276 4 11 37 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 276
  (Polychromatic418967fa.accept_9_7_4_6_1_273 43 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 276 2 21 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 276 (accept_3_5 41 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 276 4 10 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 148 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 276 2 19 74 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 276 4 9 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 148 276 (accept_3_5 35 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  148 276 2 17 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 148 276 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 148 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 276 4 8 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 276 (Polychromatic418967fa.accept_21_10_1_3_1_8092
  31 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 148 276 2 15 74 138
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 148 276
  (accept_3_5 29 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 148 276 4 7 37 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 148 276
  (Polychromatic418967fa.accept_13_1_5_3_1_888 27 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 148 276 2 13 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 148 276 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 148 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 148 276 4 6 37 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 148 276 (accept_3_5 23 148 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 148 276 2 11 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 148 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 21
  148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 276 4 5 37 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 276
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 276 2 9 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 148 276 (accept_3_5 17 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 148 276 4 4 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 148 276 (Polychromatic418967fa.accept_13_2_5_3_1_406 15 148 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 276 2 7 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 276 (Polychromatic418967fa.accept_10_3_8_6_1_326
  13 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 276 4 3 37 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 276
  (accept_3_5 11 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 276 2 5 74 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 276
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 276 4 2 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 276 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 148 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 276 2 3 74 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 276 (accept_3_5 5 148 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148 276 4 1 37 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 148 276 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 148 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 276 2 1 74 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 276
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 148 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 148
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 130 147 276 (Eq.refl Bool.true) (allA_succ_of_gcd 129 147 276 3 43 49 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 128 147 276
  (Polychromatic418967fa.accept_9_2_3_6_1_88 128 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 147 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 127 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 147 276 3 42 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 147 276 (Polychromatic418967fa.accept_9_8_3_6_1_533
  125 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 147 276
  (Polychromatic418967fa.accept_9_7_3_6_1_270 124 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 123 147 276 3 41 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 122 147 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 122 147 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 147 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 121 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 147 276 3 40 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 147 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 119 147 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 147 276
  (Polychromatic418967fa.accept_9_1_3_6_1_70 118 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 117 147 276 3 39 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 116 147 276 (Polychromatic418967fa.accept_9_8_3_6_1_533 116 147 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 147 276
  (Polychromatic418967fa.accept_9_7_3_6_1_270 115 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 147 276 3 38 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 147 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 113 147 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 147 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 112 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 111 147 276 3 37 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 110 147 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 110 147 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 147 276 (Polychromatic418967fa.accept_9_1_3_6_1_70
  109 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 147 276 3 36 49 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 147 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 107 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 147 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 106 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 147 276 3 35 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 147 276 (Polychromatic418967fa.accept_9_5_3_6_1_269
  104 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 147 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 103 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 147 276 3 34 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 147 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 101 147 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 147 276 (Polychromatic418967fa.accept_9_1_3_6_1_70
  100 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 99 147 276 3 33 49 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 147 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 98 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 147 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 97 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 147 276 3 32 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 147 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 95
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 147 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 94 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 147 276 3 31 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 147 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 92 147 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 147 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 91
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 147 276 3 30 49 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 147 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 89 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 147 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 88 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 147 276 3 29 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 147 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 86
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 85 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 147 276 3 28 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 147 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 147 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 82
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 147 276 3 27 49 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 147 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 80 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 147 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 79 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 147 276 3 26 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 147 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 77
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 76 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 147 276 3 25 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 147 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 147 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 73
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 147 276 3 24 49 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 147 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 71 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 147 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 147 276 3 23 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 147 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 147 276 3 22 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 147 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 147 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 64
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 147 276 3 21 49 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 147 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 62 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 147 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 147 276 3 20 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 147 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 147 276 3 19 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 147 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 147 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 276 (Polychromatic418967fa.accept_8_7_3_4_1_404
  55 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 147 276 3 18 49 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 147 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 147 276 3 17 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 147 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 147 276 3 16 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 147 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 147 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 46
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 147 276 3 15 49 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 147 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 147 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 147 276 3 14 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 147 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 147 276 3 13 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 147 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 147 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 147 276 3 12 49 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 147 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 147 276 3 11 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 147 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 276
  (Polychromatic418967fa.accept_8_7_3_4_1_404 31 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 147 276 3 10 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 147 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 147 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 147 276 3 9 49 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 276 3 8 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 23
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 147 276 3 7 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 147 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 147 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 276 3 6 49 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 276 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 276 3 5 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 147 276 3 4 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 147 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 147 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 276 3 3 49 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 276
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 276 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 276 3 2 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 276 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 147 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 276
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 147 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 147 276 3 1 49 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 147 276 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 147 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 276 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 147 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 131 146 276 (Eq.refl Bool.true) (allA_succ_of_gcd 130 146 276 2 65 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 146 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 129 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 146 276 2 64 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 146 276 (accept_3_4 127 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 146 276 2 63 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 146 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 125 146 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 146 276 2 62 73 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 146 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 123 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 146 276 2 61 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 146 276 (accept_3_4 121 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 146 276 2 60 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 146 276 (Polychromatic418967fa.accept_19_5_13_10_1_11674 119 146 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 146 276 2 59 73 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 146 276
  (Polychromatic418967fa.accept_17_15_10_4_1_8540 117 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 146 276 2 58 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 146 276 (accept_3_4 115 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 146 276 2 57 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 146 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 113 146 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 146 276 2 56 73 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 146 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 111 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 146 276 2 55 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 146 276 (accept_3_4 109 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 146 276 2 54 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 146 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 107 146 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 146 276 2 53 73 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 146 276
  (Polychromatic418967fa.accept_22_17_14_12_1_12335 105 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 146 276 2 52 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 146 276 (accept_3_4 103 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 146 276 2 51 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 146 276 (Polychromatic418967fa.accept_11_2_3_1_1_244 101 146 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 146 276 2 50 73 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 146 276
  (Polychromatic418967fa.accept_15_9_11_6_1_637 99 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 146 276 2 49 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 146 276 (accept_3_4 97 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 146 276 2 48 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 146 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 95 146 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 146 276 2 47 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 146 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 93 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 146 276 2 46 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 146 276 (accept_3_4 91 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 146 276 2 45 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 146 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 89 146 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 146 276 2 44 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 146 276
  (Polychromatic418967fa.accept_14_3_6_10_1_752 87 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 146 276 2 43 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 146 276 (accept_3_4 85 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 146 276 2 42 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 146 276 (Polychromatic418967fa.accept_17_15_10_4_1_8540 83 146 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 146 276 2 41 73 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 146 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 81 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 146 276 2 40 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 146 276 (accept_3_4 79 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 146 276 2 39 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 146 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 77 146 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 146 276 2 38 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 146 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 75 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 146 276 2 37 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 146 276 (accept_3_4 73 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 146 276 2 36 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 146 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 71 146 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 276 2 35 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 276
  (Polychromatic418967fa.accept_15_9_11_6_1_637 69 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 146 276 2 34 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 146 276 (accept_3_4 67 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 276 2 33 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 146 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 276 2 32 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 276
  (Polychromatic418967fa.accept_15_3_11_6_1_3083 63 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 146 276 2 31 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 146 276 (accept_3_4 61 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 276 2 30 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 146 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 276 2 29 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 57 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 276 2 28 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 276 (accept_3_4 55 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 276 2 27 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 146 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 276 2 26 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 276 2 25 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 276 (accept_3_4 49 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 276 2 24 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 276 (Polychromatic418967fa.accept_15_2_11_6_1_2135 47 146 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 276 2 23 73 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 276
  (Polychromatic418967fa.accept_14_3_6_10_1_752 45 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 276 2 22 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 276 (accept_3_4 43 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 276 2 21 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 146 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 276 2 20 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 276
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 276 2 19 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 276 (accept_3_4 37 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 276 2 18 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 146 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 276 2 17 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 276
  (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 276 2 16 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 276 (accept_3_4 31 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 276 2 15 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 276 (Polychromatic418967fa.accept_25_4_21_1_1_16962 29 146 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 276 2 14 73 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 276
  (Polychromatic418967fa.accept_18_9_2_6_1_9322 27 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 276 2 13 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 276 (accept_3_4 25 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 276 2 12 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 276 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 146 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 276 2 11 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 276
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 276 2 10 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 276 (accept_3_4 19 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 276 2 9 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 276 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 146 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 276 2 8 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 276
  (Polychromatic418967fa.accept_17_15_10_4_1_8540 15 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 146 276 2 7 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 146 276 (accept_3_4 13 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 276 2 6 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 276 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 146 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 276 2 5 73 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 276
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 276 2 4 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 276 (accept_3_4 7 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  276 2 3 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 276 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 146 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 276 2 2 73 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 276 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 146 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 276 2 1 73 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 276 (accept_3_4 1 146 276
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 132 145 276 (Eq.refl Bool.true) (allA_succ_of_accept 131 145 276 (accept_3_5 131 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 145 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 130 145
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 145 276
  (Polychromatic418967fa.accept_9_3_1_6_1_86 129 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 145 276 (accept_3_5 128 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  127 145 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 127 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 145 276 (Polychromatic418967fa.accept_13_9_2_3_1_3027 126 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 145 276 (accept_3_5 125 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 145 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 124 145
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 145 276
  (Polychromatic418967fa.accept_15_3_10_6_1_632 123 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 145 276 (accept_3_5 122 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  121 145 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 121 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 145 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 120 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 145 276 (accept_3_5 119 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 145 276 (Polychromatic418967fa.accept_13_1_2_3_1_911 118 145
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 145 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 117 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 145 276 (accept_3_5 116 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 145 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 115 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 145 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 114 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 145 276 (accept_3_5 113 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 145 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 112 145
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 145 276
  (Polychromatic418967fa.accept_9_3_1_6_1_86 111 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 145 276 (accept_3_5 110 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 145 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 109 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 145 276 (Polychromatic418967fa.accept_15_3_10_6_1_632 108 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 145 276 (accept_3_5 107 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 145 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 106 145
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 145 276
  (Polychromatic418967fa.accept_13_1_2_3_1_911 105 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 145 276 (accept_3_5 104 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 145 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 103 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 145 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 102 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 145 276 (accept_3_5 101 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 145 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 145
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 145 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 99 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 145 276 (accept_3_5 98 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 145 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 97 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 145 276 (Polychromatic418967fa.accept_13_5_2_3_1_1526 96 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 145 276 (accept_3_5 95 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 145 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 94 145 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 145 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 93 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 145 276 (accept_3_5 92 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 145 276 (Polychromatic418967fa.accept_10_1_5_6_1_649 91 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 145 276 (Polychromatic418967fa.accept_13_12_2_3_1_1527 90 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 145 276 (accept_3_5 89 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 145 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 88 145 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 145 276
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 87 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 145 276 (accept_3_5 86 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 145 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 145 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 84 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 145 276 (accept_3_5 83 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 145 276 (Polychromatic418967fa.accept_14_12_5_10_1_2130 82 145 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 145 276
  (Polychromatic418967fa.accept_10_1_5_6_1_649 81 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 145 276 (accept_3_5 80 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 145 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 145 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 145 276 (accept_3_5 77 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 145 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 145 276
  (Polychromatic418967fa.accept_9_3_1_6_1_86 75 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 145 276 (accept_3_5 74 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 145 276 (Polychromatic418967fa.accept_25_23_20_1_1_16961 73 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 145 276 (accept_3_5 71 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 145 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 145 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 145 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 69 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 145 276 (accept_3_5 68 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 145 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 145 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 66 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 145 276 (accept_3_5 65 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 145 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 276
  (Polychromatic418967fa.accept_13_11_2_3_1_883 63 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 145 276 (accept_3_5 62 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 145 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 145 276 (Polychromatic418967fa.accept_16_12_1_4_1_5403 60 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 145 276 (accept_3_5 59 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 145 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 276 (accept_3_5 56 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 145 276 (Polychromatic418967fa.accept_19_17_12_10_1_7404 55 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 145 276 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 276 (accept_3_5 53 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 145 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 145 276 (accept_3_5 50 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 145 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 276 (accept_3_5 47 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 276 (Polychromatic418967fa.accept_15_1_10_6_1_631 46 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 45 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 276 (accept_3_5 44 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 276 (Polychromatic418967fa.accept_15_12_10_6_1_2134 42 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 276 (accept_3_5 41 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 145 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 276
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 276 (accept_3_5 38 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 276 (accept_3_5 35 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 276
  (Polychromatic418967fa.accept_15_3_10_6_1_632 33 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 276 (accept_3_5 32 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 276 (accept_3_5 29 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 276 (Polychromatic418967fa.accept_16_12_1_4_1_5403 28 145 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 276
  (Polychromatic418967fa.accept_13_1_2_3_1_911 27 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 276 (accept_3_5 26 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 276 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 276 (accept_3_5 23 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 145 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 276
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 276 (accept_3_5 20 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 276 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 276 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 276 (accept_3_5 17 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 276 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 145 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 276
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 276 (accept_3_5 14 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 276 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 276 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 276 (accept_3_5 11 145 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 276 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 145 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 276
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 276 (accept_3_5 8 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 276 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 276 (Polychromatic418967fa.accept_19_6_12_10_1_4683 6 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 276 (accept_3_5 5 145 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 276 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 145 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 276
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 276 (accept_3_5 2 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 276 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 145 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 133 144 276 (Eq.refl Bool.true) (allA_succ_of_gcd 132 144 276 12 11 12 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 144 276
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 131 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 130 144 276 2 65 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 129 144 276 3 43 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 128 144 276 4 32 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 144 276 (Polychromatic418967fa.accept_7_1_4_3_1_21
  127 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 144 276 6 21 24 46
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 144 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 125 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 144 276 4 31 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 123 144 276 3 41 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 122 144 276 2 61 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 144 276 (Polychromatic418967fa.accept_13_4_1_3_1_3058 121 144
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 144 276 12 10 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 144 276
  (Polychromatic418967fa.accept_13_2_1_3_1_419 119 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 144 276 2 59 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 117 144 276 3 39 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 116 144 276 4 29 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 144 276 (Polychromatic418967fa.accept_10_5_4_6_1_319 115 144
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 144 276 6 19 24 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 144 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 113 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 144 276 4 28 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 111 144 276 3 37 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 110 144 276 2 55 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 144 276 (Polychromatic418967fa.accept_13_5_1_3_1_878 109 144
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 144 276 12 9 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 144 276
  (Polychromatic418967fa.accept_19_12_11_10_1_6024 107 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 144 276 2 53 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 105 144 276 3 35 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 144 276 4 26 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 144 276 (Polychromatic418967fa.accept_17_1_8_4_1_1519
  103 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 144 276 6 17 24 46
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 144 276
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 101 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 144 276 4 25 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 99 144 276 3 33 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 98 144 276 2 49 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 144 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 97
  144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 144 276 12 8 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 144 276
  (Polychromatic418967fa.accept_10_5_4_6_1_319 95 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 144 276 2 47 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 144 276 3 31 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 144 276 4 23 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 144 276 (Polychromatic418967fa.accept_14_7_4_10_1_1351 91 144
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 144 276 6 15 24 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 144 276
  (Polychromatic418967fa.accept_13_11_1_3_1_910 89 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 144 276 4 22 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 87 144 276 3 29 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 144 276 2 43 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 144 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 144 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 144 276 12 7 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 144 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 83 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 144 276 2 41 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 144 276 3 27 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 80 144 276 4 20 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 144 276 (Polychromatic418967fa.accept_15_4_9_6_1_627 79 144 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 144 276 6 13 24 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 144 276
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 77 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 144 276 4 19 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 144 276 3 25 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 144 276 2 37 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 276 (Polychromatic418967fa.accept_21_10_18_3_1_11147 73 144
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 144 276 12 6 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 144 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 144 276 2 35 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 144 276 3 23 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 144 276 4 17 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 276 (Polychromatic418967fa.accept_13_2_1_3_1_419 67 144 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 144 276 6 11 24 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 144 276
  (Polychromatic418967fa.accept_10_5_4_6_1_319 65 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 144 276 4 16 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 144 276 3 21 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 144 276 2 31 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 276 (Polychromatic418967fa.accept_15_1_9_6_1_1323 61 144
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 144 276 12 5 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 144 276
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 59 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 144 276 2 29 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 144 276 3 19 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 144 276 4 14 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 144 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 144 276 6 9 24 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 144 276
  (Polychromatic418967fa.accept_19_15_11_10_1_2206 53 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 144 276 4 13 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 51 144 276 3 17 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 144 276 2 25 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 276 (Polychromatic418967fa.accept_14_7_4_10_1_1351
  49 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 144 276 12 4 12 23
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 144 276
  (Polychromatic418967fa.accept_17_13_8_4_1_2514 47 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 144 276 2 23 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 144 276 3 15 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 144 276 4 11 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 276 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 144 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 144 276 6 7 24 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 144 276
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 276 4 10 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 144 276 3 13 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 144 276 2 19 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 276 (Polychromatic418967fa.accept_13_11_1_3_1_910 37 144
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 276 12 3 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 276
  (Polychromatic418967fa.accept_10_5_4_6_1_319 35 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 144 276 2 17 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 144 276 3 11 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 144 276 4 8 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 144 276 (Polychromatic418967fa.accept_13_5_1_3_1_878 31 144 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 276 6 5 24 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 276 4 7 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 144 276 3 9 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 144 276 2 13 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 276 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 144 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 276 12 2 12 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 276
  (Polychromatic418967fa.accept_21_2_18_3_1_9697 23 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 144 276 2 11 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 144 276 3 7 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 144 276 4 5 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 144 276 (Polychromatic418967fa.accept_13_6_1_3_1_1522 19 144 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 276 6 3 24 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 276
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 276 4 4 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 144 276 3 5 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 144 276 2 7 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 144 276 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 144 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 276 12 1 12 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 276
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 276 2 5 72 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 144 276 3 3 48 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 144 276 4 2 36 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 144 276 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 144 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 276 6 1 24 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 276 (Polychromatic418967fa.accept_10_5_4_6_1_319 5
  144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 276 4 1 36 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 276 3 1 48 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 276 2 1 72 138 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 276
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 144 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 144
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 134 143 276 (Eq.refl Bool.true) (allA_succ_of_accept 133 143 276 (accept_3_4 133 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 143 276 (Polychromatic418967fa.accept_14_6_3_10_1_3905 132
  143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 143 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 131 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 143 276 (accept_3_4 130 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 143 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 129 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 143 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 128 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 143 276 (accept_3_4 127 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 143 276 (Polychromatic418967fa.accept_16_14_15_4_1_3268 126
  143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 143 276
  (Polychromatic418967fa.accept_14_13_3_10_1_2159 125 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 124 143 276 (accept_3_4 124 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 143 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 123 143 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 143 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 122 143
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 143 276 (accept_3_4 121 143
  276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 143 276
  (Polychromatic418967fa.accept_9_3_8_6_1_80 120 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 143 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 119 143 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 143 276 (accept_3_4 118 143 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 143 276 (Polychromatic418967fa.accept_10_7_3_6_1_644 117 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 143 276
  (Polychromatic418967fa.accept_17_14_7_4_1_3476 116 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 143 276 (accept_3_4 115 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 143 276 (Polychromatic418967fa.accept_17_12_7_4_1_7231 114 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 143 276 (Polychromatic418967fa.accept_9_5_8_6_1_281
  113 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 143 276 (accept_3_4
  112 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 143 276
  (Polychromatic418967fa.accept_9_3_8_6_1_80 111 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 143 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 110 143 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 143 276 (accept_3_4 109 143 276 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 143 276 (Polychromatic418967fa.accept_10_8_3_6_1_685 108 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 143 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 107 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 143 276 (accept_3_4 106 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 143 276 (Polychromatic418967fa.accept_14_7_3_10_1_1364 105 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 143 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 104 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 143 276 (accept_3_4 103 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 143 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 102 143
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 143 276
  (Polychromatic418967fa.accept_9_2_8_6_1_79 101 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 143 276 (accept_3_4 100 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 143 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 99 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 143 276 (Polychromatic418967fa.accept_10_8_3_6_1_685 98 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 143 276 (accept_3_4 97 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 143 276 (Polychromatic418967fa.accept_21_12_17_3_1_11145 96
  143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 143 276
  (Polychromatic418967fa.accept_9_5_8_6_1_281 95 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 143 276 (accept_3_4 94 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 143 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 93 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 143 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 92 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 143 276 (accept_3_4 91 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 143 276 (Polychromatic418967fa.accept_14_6_3_10_1_3905 90 143 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 143 276
  (Polychromatic418967fa.accept_10_9_3_6_1_686 89 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 143 276 (accept_3_4 88 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 143 276 (Polychromatic418967fa.accept_10_7_3_6_1_644 87 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 143 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 86 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 143 276 (accept_3_4 85 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 143 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 84 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 83 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 143 276 (accept_3_4 82 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 143 276 (Polychromatic418967fa.accept_21_18_17_3_1_4906 81 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 143 276 (Polychromatic418967fa.accept_17_12_7_4_1_7231 80 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 276 (accept_3_4 79 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 143 276 (Polychromatic418967fa.accept_10_8_3_6_1_685 78 143
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 143 276
  (Polychromatic418967fa.accept_9_5_8_6_1_281 77 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 143 276 (accept_3_4 76 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 143 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 143 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 74 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 276 (accept_3_4 73 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 276 (Polychromatic418967fa.accept_16_8_15_4_1_5402 72 143 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 143 276
  (Polychromatic418967fa.accept_17_3_7_4_1_7230 71 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 143 276 (accept_3_4 70 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 143 276 (Polychromatic418967fa.accept_10_9_3_6_1_686 69 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 143 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 68 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 143 276 (accept_3_4 67 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 143 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 143 276
  (Polychromatic418967fa.accept_9_2_8_6_1_79 65 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 143 276 (accept_3_4 64 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 143 276 (Polychromatic418967fa.accept_14_7_3_10_1_1364 63 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 143 276 (Polychromatic418967fa.accept_14_6_3_10_1_3905 62 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 276 (accept_3_4 61 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 276 (Polychromatic418967fa.accept_16_12_15_4_1_5422 60 143
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 143 276 (accept_3_4 58 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 143 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 143 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 56 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 276 (accept_3_4 55 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 143 276 (Polychromatic418967fa.accept_17_3_7_4_1_7230 54 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 276
  (Polychromatic418967fa.accept_16_5_15_4_1_9099 53 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 143 276 (accept_3_4 52 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 143 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 143 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 50 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 276 (accept_3_4 49 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 276
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 143 276 (accept_3_4 46 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 143 276 (Polychromatic418967fa.accept_22_1_11_12_1_7713 45 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 143 276 (Polychromatic418967fa.accept_15_14_8_6_1_2133 44 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 276 (accept_3_4 43 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 276 (Polychromatic418967fa.accept_17_8_7_4_1_8617 42 143
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 276
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 276 (accept_3_4 40 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 143 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 276 (accept_3_4 37 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 276 (Polychromatic418967fa.accept_21_15_17_3_1_3373 36 143 276
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 276 (accept_3_4 34 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 276 (Polychromatic418967fa.accept_18_15_17_6_1_4043 33 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 276 (accept_3_4 31 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 276
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 276 (accept_3_4 28 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 276 (Polychromatic418967fa.accept_22_4_11_12_1_7692 26 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 276 (accept_3_4 25 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 276 (Polychromatic418967fa.accept_16_8_15_4_1_5402 24 143
  276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 276
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 276 (accept_3_4 22 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 276 (accept_3_4 19 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 276 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 276
  (Polychromatic418967fa.accept_10_7_3_6_1_644 17 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 276 (accept_3_4 16 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 276 (Polychromatic418967fa.accept_18_15_17_6_1_4043 15 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 276 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 276 (accept_3_4 13 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 276 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 276
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 276 (accept_3_4 10 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 276 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 276 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 276 (accept_3_4 7 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 276 (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 143 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 276
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 276 (accept_3_4 4 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 276 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 143 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 276 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 276 (accept_3_4 1 143 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143
  276))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 135 142 276 (Eq.refl Bool.true) (allA_succ_of_gcd 134 142 276 2 67 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 142 276
  (Polychromatic418967fa.accept_15_13_7_6_1_682 133 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 142 276 2 66 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 142 276 (accept_3_5 131 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 142 276 2 65 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 142 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 129 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 142 276 2 64 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 142 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 127 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 142 276 2 63 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 142 276 (accept_3_5 125 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 142 276 2 62 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 142 276 (Polychromatic418967fa.accept_11_2_10_1_1_1017 123 142 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 142 276 2 61 71 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 142 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 121 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 142 276 2 60 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 142 276 (accept_3_5 119 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 142 276 2 59 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 142 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 117 142 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 142 276 2 58 71 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 142 276
  (Polychromatic418967fa.accept_19_1_9_10_1_10391 115 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 114 142 276 2 57 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 113 142 276 (accept_3_5 113 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 142 276 2 56 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 142 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 111 142 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 142 276 2 55 71 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 142 276
  (Polychromatic418967fa.accept_9_1_7_6_1_75 109 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 142 276 2 54 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 142 276 (accept_3_5 107 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 142 276 2 53 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 142 276 (Polychromatic418967fa.accept_16_9_14_4_1_3225 105 142 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 142 276 2 52 71 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 142 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 103 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 142 276 2 51 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 142 276 (accept_3_5 101 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 142 276 2 50 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 142 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 99 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 142 276 2 49 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 142 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 97 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 142 276 2 48 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 142 276 (accept_3_5 95 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 142 276 2 47 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 142 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 93 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 142 276 2 46 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 142 276
  (Polychromatic418967fa.accept_9_1_7_6_1_75 91 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 142 276 2 45 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 142 276 (accept_3_5 89 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 142 276 2 44 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 142 276 (Polychromatic418967fa.accept_13_9_12_3_1_907 87 142 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 142 276 2 43 71 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 142 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 85 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 142 276 2 42 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 142 276 (accept_3_5 83 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 142 276 2 41 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 142 276 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 142 276 2 40 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 142 276
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 79 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 142 276 2 39 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 142 276 (accept_3_5 77 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 142 276 2 38 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 142 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 142 276 2 37 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 142 276
  (Polychromatic418967fa.accept_9_1_7_6_1_75 73 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 142 276 2 36 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 142 276 (accept_3_5 71 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 142 276 2 35 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 142 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 276 2 34 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 67 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 276 2 33 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 276 (accept_3_5 65 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 276 2 32 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 276 (Polychromatic418967fa.accept_16_15_14_4_1_6649 63 142 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 276 2 31 71 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 61 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 142 276 2 30 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 142 276 (accept_3_5 59 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 276 2 29 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 276 2 28 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 276 2 27 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 276 (accept_3_5 53 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 276 2 26 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 276 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 276 2 25 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 276 2 24 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 276 (accept_3_5 47 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 276 2 23 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 276 (Polychromatic418967fa.accept_17_11_6_4_1_4729 45 142 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 276 2 22 71 138 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 276
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 276 2 21 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 276 (accept_3_5 41 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 276 2 20 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 276 2 19 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 276
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 276 2 18 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 276 (accept_3_5 35 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 276 2 17 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 276 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 276 2 16 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 276
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 276 2 15 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 276 (accept_3_5 29 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 276 2 14 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 276 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 276 2 13 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 276
  (Polychromatic418967fa.accept_16_9_14_4_1_3225 25 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 276 2 12 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 276 (accept_3_5 23 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 276 2 11 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 276 2 10 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 276
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 276 2 9 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 276 (accept_3_5 17 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 276 2 8 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 276 2 7 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 276
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 276 2 6 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 276 (accept_3_5 11 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 276 2 5 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 276 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 142 276 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 276 2 4 71 138 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 276
  (Polychromatic418967fa.accept_16_7_14_4_1_1362 7 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 276 2 3 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 276 (accept_3_5 5 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  276 2 2 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 276 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 142 276 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 276 2 1 71 138 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 276 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 142 276 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  276)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_276_segment_001)))))))))))))))))))))))))))))))))))))))))))


