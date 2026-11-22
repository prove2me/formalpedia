-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch253_Segment000
-- name    : Polychromatic418967fa_Branch253_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:40:35.373457+00:00
-- url     : https://prove2.me/theorems/20df47fa-e79a-4806-ab9c-7fc73cf4ffee
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_253_segment_000 : allB 123 253 :=
  allB_succ 122 253 (allA_of_3_1 122 122 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 121 253
  (allA_succ_of_accept 120 121 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 120 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 253 (accept_3_3 119 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 121 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 118 121 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 253
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 117 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 121 253 (accept_3_3 116 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 121 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 115 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 121 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 114 121
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 253 (accept_3_3 113 121
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 253
  (Polychromatic418967fa.accept_10_2_1_3_1_233 112 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 121 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 111 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 121 253 11 10 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 121 253 (Polychromatic418967fa.accept_13_5_4_6_1_2371
  109 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 121 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 108 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 121 253 (accept_3_3 107 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 121 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 106 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 121 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 105 121 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 121 253 (accept_3_3 104 121 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 121 253 (Polychromatic418967fa.accept_16_7_9_13_1_4948 103
  121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 121 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 102 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 121 253 (accept_3_3 101 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 121 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 100 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 99 121 253 11 9 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 98 121 253 (accept_3_3 98 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 121 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 97 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 121 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 96 121 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 253 (accept_3_3 95 121 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 253 (Polychromatic418967fa.accept_7_3_2_1_1_225
  94 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 93 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 253 (accept_3_3 92 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 253 (Polychromatic418967fa.accept_21_7_16_1_1_6298 91 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 121 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 253 (accept_3_3 89 121 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 88 121 253 11 8 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 121 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 121 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 121 253 (accept_3_3 86 121 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 121 253 (Polychromatic418967fa.accept_13_7_4_6_1_3221
  85 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 121 253
  (Polychromatic418967fa.accept_8_4_1_5_1_186 84 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 121 253 (accept_3_3 83 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 121 253 (Polychromatic418967fa.accept_10_2_1_3_1_233 82 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 121 253 (Polychromatic418967fa.accept_16_1_9_13_1_1822 81 121 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 121 253 (accept_3_3 80 121 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 121 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 121 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 121 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 78 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 121 253 11 7 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 121 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 121 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 75
  121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 121 253 (accept_3_3 74
  121 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 121 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 121 253 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 253 (accept_3_3 71 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 121 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 121 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 253 (Polychromatic418967fa.accept_7_6_2_1_1_214
  69 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 121 253 (accept_3_3 68
  121 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 121 253
  (Polychromatic418967fa.accept_13_2_4_6_1_2356 67 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 121 253 11 6 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 121 253 (accept_3_3 65 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 121 253 (Polychromatic418967fa.accept_14_8_9_1_1_3313 64 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 253 (Polychromatic418967fa.accept_13_11_4_6_1_1006 63 121
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 253 (accept_3_3 62 121
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 253
  (Polychromatic418967fa.accept_9_7_4_1_1_391 61 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 121 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 253 (accept_3_3 59 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 121 253 (Polychromatic418967fa.accept_10_8_1_3_1_1374 58 121 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 253 (accept_3_3 56 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  121 253 11 5 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 121 253 (Polychromatic418967fa.accept_13_2_4_6_1_2356 54 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 253 (accept_3_3 53 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 121 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 121 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 253 (Polychromatic418967fa.accept_9_6_4_1_1_390
  51 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 253 (accept_3_3 50
  121 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 121 253
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 49 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 121 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 253 (accept_3_3 47 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 121 253 (Polychromatic418967fa.accept_13_7_4_6_1_3221 46 121 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 121 253 11 4 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 121 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 121 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 253 (Polychromatic418967fa.accept_9_6_4_1_1_390
  42 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 253 (accept_3_3 41
  121 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 253
  (Polychromatic418967fa.accept_15_10_1_13_1_2609 40 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 121 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 121 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 253 (accept_3_3 38 121 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 253 (Polychromatic418967fa.accept_13_11_4_6_1_1006 37 121 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 253
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 121 253 (accept_3_3 35 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 121 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 121 253 11 3 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 121 253 (accept_3_3 32 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 121 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 121 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 253 (accept_3_3 29 121 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 253 (Polychromatic418967fa.accept_8_4_1_5_1_186
  28 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 253 (accept_3_3 26 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 121 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 253 (accept_3_3 23 121 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 121 253 11 2 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 121 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 121 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 253 (accept_3_3 20 121 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 253
  (Polychromatic418967fa.accept_21_19_16_1_1_2053 19 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 253 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 121 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 253 (accept_3_3 17 121 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 121 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 253 (accept_3_3 14 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 121 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 121 253 11 1 11 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 121 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 10 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 121 253 (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 253 (accept_3_3 8 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 121 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 121 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 6
  121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 253 (accept_3_3 5 121
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 253
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 121 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 121 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 253 (accept_3_3 2 121 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 121 253 (Polychromatic418967fa.accept_16_1_9_13_1_1822 1 121 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 253 (allA_succ_of_accept 119 120 253 (accept_3_3 119 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 120 253 (Polychromatic418967fa.accept_13_1_3_6_1_158 118 120 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 120 253 (Polychromatic418967fa.accept_16_5_8_13_1_2764 117
  120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 253 (accept_3_3 116
  120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 120 253
  (Polychromatic418967fa.accept_9_7_3_1_1_386 115 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 120 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 114 120 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 120 253 (accept_3_3 113 120 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 120 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 112 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 253
  (Polychromatic418967fa.accept_17_9_1_15_1_3156 111 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 120 253 (accept_3_3 110 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 120 253 (Polychromatic418967fa.accept_13_5_3_6_1_3278 109 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 120 253
  (Polychromatic418967fa.accept_16_12_8_13_1_6073 108 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 120 253 (accept_3_3 107 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 120 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 106 120 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 120 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 105 120
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 120 253 (accept_3_3 104 120
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 120 253
  (Polychromatic418967fa.accept_9_4_3_1_1_154 103 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 120 253 (Polychromatic418967fa.accept_21_18_15_1_1_9470 102 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 120 253 (accept_3_3 101 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 253 (Polychromatic418967fa.accept_13_9_3_6_1_1661 100 120 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 253
  (Polychromatic418967fa.accept_16_3_8_13_1_3867 99 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 120 253 (accept_3_3 98 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 120 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 97 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 120 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 96 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 120 253 (accept_3_3 95 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 120 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 94 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 253
  (Polychromatic418967fa.accept_14_9_8_1_1_2381 93 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 120 253 (accept_3_3 92 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 120 253 (Polychromatic418967fa.accept_14_7_8_1_1_1621 91 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 120 253 (Polychromatic418967fa.accept_21_6_15_1_1_2050 90 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 120 253 (accept_3_3 89 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 88 120 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 87 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 120 253 (accept_3_3 86 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 120 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 85 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 120 253 (Polychromatic418967fa.accept_16_4_8_13_1_1059 84 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 120 253 (accept_3_3 83 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 253 (Polychromatic418967fa.accept_21_19_15_1_1_6345 82 120
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 253
  (Polychromatic418967fa.accept_21_18_15_1_1_9470 81 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 120 253 (accept_3_3 80 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 120 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 120 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 120 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 78 120 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 120 253 (accept_3_3 77 120 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 253 (Polychromatic418967fa.accept_9_4_3_1_1_154
  76 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 120 253
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 75 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 120 253 (accept_3_3 74 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 120 253 (Polychromatic418967fa.accept_21_10_15_1_1_9494 73 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 120 253 (Polychromatic418967fa.accept_14_2_8_1_1_1647 72 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 120 253 (accept_3_3 71 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 120 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 120 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 69 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 120 253 (accept_3_3 68 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 120 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 120 253 (Polychromatic418967fa.accept_13_1_3_6_1_158 66 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 120 253 (accept_3_3 65 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 253 (Polychromatic418967fa.accept_35_29_15_8_1_15441 64
  120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 253
  (Polychromatic418967fa.accept_14_7_8_1_1_1621 63 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 120 253 (accept_3_3 62 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 120 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 120 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 120 253 (accept_3_3 59 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 253
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 57 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 120 253 (accept_3_3 56 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 120 253 (Polychromatic418967fa.accept_25_5_20_3_1_15440 55 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 120 253 (Polychromatic418967fa.accept_17_3_1_15_1_6835 54 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 120 253 (accept_3_3 53 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 120 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 120 253 (accept_3_3 50 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 120 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 120 253 (Polychromatic418967fa.accept_13_9_3_6_1_1661 48 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 253 (accept_3_3 47 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 253 (Polychromatic418967fa.accept_17_12_1_15_1_5472 46 120
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 253
  (Polychromatic418967fa.accept_21_3_15_1_1_2046 45 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 120 253 (accept_3_3 44 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 120 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 120 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 120 253 (accept_3_3 41 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 253
  (Polychromatic418967fa.accept_18_3_12_1_1_3787 39 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 120 253 (accept_3_3 38 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 120 253 (Polychromatic418967fa.accept_14_9_8_1_1_2381 37 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 120 253 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 120 253 (accept_3_3 35 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 120 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 120 253 (accept_3_3 32 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 120 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 120 253 (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 120 253 (accept_3_3 29 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 253 (Polychromatic418967fa.accept_16_12_8_13_1_6073 28 120
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 253
  (Polychromatic418967fa.accept_13_1_3_6_1_158 27 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 120 253 (accept_3_3 26 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 120 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 120 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 253 (accept_3_3 23 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 253
  (Polychromatic418967fa.accept_14_7_8_1_1_1621 21 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 120 253 (accept_3_3 20 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 120 253 (Polychromatic418967fa.accept_16_3_8_13_1_3867 19 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 120 253 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 253 (accept_3_3 17 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 120 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 120 253 (accept_3_3 14 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 120 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 120 253 (Polychromatic418967fa.accept_16_12_8_13_1_6073 12 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 253 (accept_3_3 11 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 253 (Polychromatic418967fa.accept_13_10_3_6_1_1003 10 120
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 253
  (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 120 253 (accept_3_3 8 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  120 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 120 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 253 (accept_3_3 5 120 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 120 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 253
  (Polychromatic418967fa.accept_16_3_8_13_1_3867 3 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 120 253 (accept_3_3 2 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  120 253 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 120 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 120
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 253 (allA_of_3_1 119 119 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 118 253
  (allA_succ_of_accept 117 118 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 117 118 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 118 253 (accept_3_3 116 118 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 115 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 118 253
  (Polychromatic418967fa.accept_7_2_6_1_1_73 114 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 118 253 (accept_3_3 113 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 118 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 112 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 118 253 (accept_3_3 110 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 118 253 (Polychromatic418967fa.accept_13_5_1_6_1_2367 109 118
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 118 253
  (Polychromatic418967fa.accept_19_13_4_6_1_9960 108 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 118 253 (accept_3_3 107 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 118 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 106 118 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 118 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 118 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 118 253 (accept_3_3 104 118 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50
  103 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 118 253
  (Polychromatic418967fa.accept_20_2_18_13_1_3843 102 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 118 253 (accept_3_3 101 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 118 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 100 118 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 118 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 118 253 (accept_3_3 98 118 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 118 253 (Polychromatic418967fa.accept_19_2_4_6_1_5738
  97 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 118 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 96 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 118 253 (accept_3_3 95 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 118 253 (Polychromatic418967fa.accept_13_3_1_6_1_509 94 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 118 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 118 253 (accept_3_3 92 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 118 253
  (Polychromatic418967fa.accept_22_2_8_11_1_12275 90 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 118 253 (accept_3_3 89 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 118 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 88 118 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 118 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 118 253 (accept_3_3 86 118 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 118 253 (Polychromatic418967fa.accept_10_5_8_3_1_229
  85 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 118 253
  (Polychromatic418967fa.accept_16_4_6_13_1_1874 84 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 118 253 (accept_3_3 83 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 118 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 82 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 118 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 118 253 (accept_3_3 80 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 118 253
  (Polychromatic418967fa.accept_19_2_4_6_1_5738 78 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 118 253 (accept_3_3 77 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 118 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 76 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 118 253 (accept_3_3 74 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 118 253 (Polychromatic418967fa.accept_13_8_1_6_1_997 73 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 118 253
  (Polychromatic418967fa.accept_7_2_6_1_1_73 72 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 118 253 (accept_3_3 71 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 118 253 (Polychromatic418967fa.accept_13_5_1_6_1_2367 70 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 118 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 253 (accept_3_3 68 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 253
  (Polychromatic418967fa.accept_10_6_8_3_1_930 66 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 253 (accept_3_3 65 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 253 (accept_3_3 62 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 253
  (Polychromatic418967fa.accept_13_8_1_6_1_997 60 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 253 (accept_3_3 59 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 253 (accept_3_3 56 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 118 253 (accept_3_3 53 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 253 (accept_3_3 50 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 253 (Polychromatic418967fa.accept_14_7_6_1_1_1656 49 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 253
  (Polychromatic418967fa.accept_13_9_1_6_1_510 48 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 253 (accept_3_3 47 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 46 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 253 (accept_3_3 44 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 253
  (Polychromatic418967fa.accept_13_3_1_6_1_509 42 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 253 (accept_3_3 41 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 253 (accept_3_3 38 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 253
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 118 253 (accept_3_3 35 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 118 253 (Polychromatic418967fa.accept_13_8_1_6_1_997 34 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 118 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 253 (accept_3_3 32 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 253
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 253 (accept_3_3 29 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 253 (accept_3_3 26 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 253 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 253
  (Polychromatic418967fa.accept_19_5_4_6_1_11375 24 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 253 (accept_3_3 23 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 253 (Polychromatic418967fa.accept_13_9_1_6_1_510 22 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 253 (accept_3_3 20 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 253
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 253 (accept_3_3 17 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 253 (accept_3_3 14 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 253 (Polychromatic418967fa.accept_18_13_10_1_1_9025 13 118 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 253 (accept_3_3 11 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 253 (Polychromatic418967fa.accept_19_10_4_6_1_11376 10 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 253 (accept_3_3 8 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 253
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 253 (accept_3_3 5 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 118 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 253 (accept_3_3 2 118 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 253 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 118 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 253 (allA_succ_of_accept 116 117 253 (accept_3_3 116 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 117 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 115 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 253 (Polychromatic418967fa.accept_10_4_7_3_1_54 114 117
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 253 (accept_3_3 113 117
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 253
  (Polychromatic418967fa.accept_6_4_3_1_1_57 112 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 117 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 111 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 253 (accept_3_3 110 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 117 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 109 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 108 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 117 253 (accept_3_3 107 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 106 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 117 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 105 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 253 (accept_3_3 104 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 253 (Polychromatic418967fa.accept_19_8_3_6_1_9982 103 117
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 102 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 117 253 (accept_3_3 101 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 117 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 99 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 253 (accept_3_3 98 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 97 117 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 253
  (Polychromatic418967fa.accept_10_6_7_3_1_547 96 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 117 253 (accept_3_3 95 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 117 253 (Polychromatic418967fa.accept_15_3_12_13_1_2549 93 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 253 (accept_3_3 92 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 253 (Polychromatic418967fa.accept_15_1_12_13_1_944 91 117
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 90 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 117 253 (accept_3_3 89 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 117 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 253 (accept_3_3 86 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 85 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 253
  (Polychromatic418967fa.accept_10_4_7_3_1_54 84 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 117 253 (accept_3_3 83 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 117 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 253 (accept_3_3 80 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 253 (Polychromatic418967fa.accept_24_7_21_13_1_13668 79 117 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 253
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 78 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 117 253 (accept_3_3 77 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 75 117
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 253 (accept_3_3 74 117
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 117 253 (Polychromatic418967fa.accept_16_8_5_13_1_1021 72 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 253 (accept_3_3 71 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 253 (Polychromatic418967fa.accept_7_6_5_1_1_416
  69 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 253 (accept_3_3 68
  117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 117 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 253 (accept_3_3 65 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 253 (Polychromatic418967fa.accept_12_3_9_1_1_290
  63 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 253 (accept_3_3 62
  117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 253
  (Polychromatic418967fa.accept_15_1_12_13_1_944 61 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 117 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 253 (accept_3_3 59 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 253
  (Polychromatic418967fa.accept_16_9_5_13_1_4972 57 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 117 253 (accept_3_3 56 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 117 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 117 253 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 253 (accept_3_3 53 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 253
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 117 253 (accept_3_3 50 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 117 253 (Polychromatic418967fa.accept_16_1_5_13_1_1025 49 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 117 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 253 (accept_3_3 47 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 117 253 (accept_3_3 44 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 117 253 (Polychromatic418967fa.accept_19_5_3_6_1_8642 43 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 117 253 (Polychromatic418967fa.accept_16_10_5_13_1_8591 42 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 253 (accept_3_3 41 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 117 253 (accept_3_3 38 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 117 253 (Polychromatic418967fa.accept_19_18_3_6_1_9989 37 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 117 253 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 253 (accept_3_3 35 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 117 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 253
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 33 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 253 (accept_3_3 32 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 253 (Polychromatic418967fa.accept_20_10_17_13_1_6773 30
  117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 253 (accept_3_3 29
  117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 253
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 117 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 253 (accept_3_3 26 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 117 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 24
  117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 253 (accept_3_3 23
  117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 253
  (Polychromatic418967fa.accept_6_4_3_1_1_57 22 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 117 253 (Polychromatic418967fa.accept_18_3_9_1_1_3690 21 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 253 (accept_3_3 20 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 117 253 (Polychromatic418967fa.accept_21_19_12_1_1_11027 19 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 253 (accept_3_3 17 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 253 (accept_3_3 14 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 117 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 253
  (Polychromatic418967fa.accept_22_12_7_11_1_15439 12 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 253 (accept_3_3 11 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 117 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 253 (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 117
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 253 (accept_3_3 8 117 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 253 (Polychromatic418967fa.accept_19_7_3_6_1_8663
  7 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 253 (accept_3_3 5 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 253 (accept_3_3 2 117 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 253 (Polychromatic418967fa.accept_15_1_12_13_1_944 1 117 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 253 (allA_of_3_1 116 116 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 115 253
  (allA_succ_of_accept 114 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 114 115 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 253 (accept_3_3 113 115 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 115 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 112 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 111 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 115 253 (accept_3_3 110 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 115 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 109 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 115 253 (Polychromatic418967fa.accept_10_8_5_3_1_543 108 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 115 253 (accept_3_3 107 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 106 115 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 115 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 105 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 115 253 (accept_3_3 104 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 115 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 103 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 115 253 (accept_3_3 101 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 115 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 100 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 115 253
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 99 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 115 253 (accept_3_3 98 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 115 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 97 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 115 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 115 253 (accept_3_3 95 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 115 253
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 115 253 23 4 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 91 115 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 91 115 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 115 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 115 253 (accept_3_3 89 115 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 88
  115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 115 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 87 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 115 253 (accept_3_3 86 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 115 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 115 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 84 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 253 (accept_3_3 83 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 115 253 (accept_3_3 80 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 115 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 115 253 (accept_3_3 77 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 115 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 115 253 (accept_3_3 74 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 115 253 (Polychromatic418967fa.accept_13_8_11_6_1_1035 73 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 115 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 253 (accept_3_3 71 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 115 253 23 3 5 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 115 253 (accept_3_3 68 115 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 115 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 67
  115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 115 253 (accept_3_3 65 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 115 253 (Polychromatic418967fa.accept_15_4_10_13_1_2565 64 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 115 253 (Polychromatic418967fa.accept_15_3_10_13_1_2605 63 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 253 (accept_3_3 62 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 115 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 115 253 (accept_3_3 59 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 115 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 253 (accept_3_3 56 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 115 253 (Polychromatic418967fa.accept_21_13_10_1_1_6292 55 115 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 253 (accept_3_3 53 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 253 (Polychromatic418967fa.accept_10_2_5_3_1_1408 52 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 253 (accept_3_3 50 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 253 (accept_3_3 47 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  115 253 23 2 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 115 253 (Polychromatic418967fa.accept_17_11_13_15_1_2140 45 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 253 (accept_3_3 44 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 115 253 (Polychromatic418967fa.accept_13_4_11_6_1_1033 43 115 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 115 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 253 (accept_3_3 41 115 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 253 (Polychromatic418967fa.accept_7_5_3_1_1_424
  40 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 253 (accept_3_3 38 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 253 (Polychromatic418967fa.accept_17_2_13_15_1_4349 36 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 253 (accept_3_3 35 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 115 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 253 (accept_3_3 32 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 253 (accept_3_3 29 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 253 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 115 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 253
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 253 (accept_3_3 26 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 115 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 23 115 253 23 1 5 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 22 115 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 115 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 115 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 253 (accept_3_3 20 115 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 115 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 253 (accept_3_3 17
  115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 253
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 115 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 115 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 253 (accept_3_3 14 115 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 115 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 253 (Polychromatic418967fa.accept_7_5_3_1_1_424
  12 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 253 (accept_3_3 11
  115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 115 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 115 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 253 (accept_3_3 8 115 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 115 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 115 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 253 (accept_3_3 5 115
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 253 (Polychromatic418967fa.accept_7_4_3_1_1_87
  4 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 253 (accept_3_3 2 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 115 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 253 (allA_succ_of_accept 113 114 253 (accept_3_3 113 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 114 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 112 114 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 111 114
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 253 (accept_3_3 110 114
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 114 253
  (Polychromatic418967fa.accept_10_9_4_3_1_539 109 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 114 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 108 114 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 114 253 (accept_3_3 107 114 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 114 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 106 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 253
  (Polychromatic418967fa.accept_17_3_12_15_1_1203 105 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 114 253 (accept_3_3 104 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 114 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 114 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 102 114
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 114 253 (accept_3_3 101 114
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 253
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 100 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 114 253 (accept_3_3 98 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 114 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 97 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 114 253
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 96 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 114 253 (accept_3_3 95 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 114 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 94 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 114 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 114 253 (accept_3_3 92 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 114 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 90 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 114 253 (accept_3_3 89 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 114 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 88 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 114 253 (accept_3_3 86 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 114 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 85 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 114 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 114 253 (accept_3_3 83 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 114 253 (Polychromatic418967fa.accept_13_4_10_6_1_989 82 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 114 253 (Polychromatic418967fa.accept_13_3_10_6_1_2382 81 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 114 253 (accept_3_3 80 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 114 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 114 253
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 78 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 114 253 (accept_3_3 77 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 114 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 114 253 (accept_3_3 74 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 114 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 114 253
  (Polychromatic418967fa.accept_22_6_4_11_1_7374 72 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 114 253 (accept_3_3 71 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 114 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 114 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 253 (accept_3_3 68 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 114 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 66 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 114 253 (accept_3_3 65 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 114 253 (Polychromatic418967fa.accept_13_12_10_6_1_3212 64 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 253 (accept_3_3 62 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 114 253
  (Polychromatic418967fa.accept_21_18_9_1_1_9467 60 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 114 253 (accept_3_3 59 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 114 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 114 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 253 (accept_3_3 56 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 253
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 54 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 114 253 (accept_3_3 53 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 114 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 253 (accept_3_3 50 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 114 253 (accept_3_3 47 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 114 253 (Polychromatic418967fa.accept_26_20_10_19_1_15438 46 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 253 (accept_3_3 44 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 114 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 253
  (Polychromatic418967fa.accept_13_3_10_6_1_2382 42 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 114 253 (accept_3_3 41 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 114 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 253 (accept_3_3 38 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 253 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 253
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 114 253 (accept_3_3 35 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 114 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 114 253 (Polychromatic418967fa.accept_15_3_9_13_1_1681 33 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 253 (accept_3_3 32 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 114 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 114 253 (accept_3_3 29 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 114 253 (Polychromatic418967fa.accept_13_2_10_6_1_1676 28 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 253 (accept_3_3 26 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 114 253 (accept_3_3 23 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 114 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 114 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 253 (accept_3_3 20 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 253
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 253 (accept_3_3 17 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 114 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 253 (accept_3_3 14 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 114 253 (accept_3_3 11 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 114 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 114 253 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 253 (accept_3_3 8 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 114 253 (accept_3_3 5 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  114 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 114 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 114 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 253 (accept_3_3 2 114 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 253 (Polychromatic418967fa.accept_17_1_12_15_1_1263 1 114 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 253 (allA_of_3_1 113 113 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 253
  (allA_succ_of_accept 111 112 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 111 112 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 112 253 (accept_3_3 110 112 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 112 253 (Polychromatic418967fa.accept_21_4_7_1_1_6307 109 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 112 253
  (Polychromatic418967fa.accept_19_13_17_6_1_11363 108 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 112 253 (accept_3_3 107 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 112 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 106 112 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 112 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 112 253 (accept_3_3 104 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 112 253
  (Polychromatic418967fa.accept_19_8_17_6_1_5728 103 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 112 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 102 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 112 253 (accept_3_3 101 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 112 253 (Polychromatic418967fa.accept_21_16_7_1_1_9430 100
  112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 112 253 (accept_3_3 98 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 112 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 97 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 112 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 96 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 112 253 (accept_3_3 95 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 112 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 94 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 112 253 (accept_3_3 92 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 112 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 91 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 112 253 (Polychromatic418967fa.accept_17_5_10_15_1_5574 90 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 112 253 (accept_3_3 89 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 112 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 112 253 (accept_3_3 86 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 112 253 (Polychromatic418967fa.accept_10_5_2_3_1_239 85 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 112 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 112 253 (accept_3_3 83 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 112 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 82 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 112 253 (accept_3_3 80 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 112 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 112 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 78 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 112 253 (accept_3_3 77 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 112 253 (Polychromatic418967fa.accept_13_11_8_6_1_1023 76 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 112 253 (accept_3_3 74 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 112 253 (Polychromatic418967fa.accept_17_5_10_15_1_5574 73 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 112 253 (Polychromatic418967fa.accept_17_4_10_15_1_5444 72 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 112 253 (accept_3_3 71 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 112 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 112 253 (accept_3_3 68 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 112 253 (Polychromatic418967fa.accept_13_2_8_6_1_2390 67 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 112 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 112 253 (accept_3_3 65 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 112 253 (Polychromatic418967fa.accept_22_20_2_11_1_10750 64 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 112 253 (accept_3_3 62 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 112 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 112 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 112 253 (accept_3_3 59 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 112 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 112 253 (accept_3_3 56 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 112 253 (Polychromatic418967fa.accept_10_5_2_3_1_239 55 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 112 253 (Polychromatic418967fa.accept_13_2_8_6_1_2390 54 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 253 (accept_3_3 53 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 253 (accept_3_3 50 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 253 (Polychromatic418967fa.accept_19_11_17_6_1_7157 49 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 253 (accept_3_3 47 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 253 (accept_3_3 44 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 112 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 253 (accept_3_3 41 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 253 (Polychromatic418967fa.accept_13_1_8_6_1_1016 40 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 112 253 (accept_3_3 38 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 112 253 (Polychromatic418967fa.accept_13_11_8_6_1_1023 37 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 112 253 (Polychromatic418967fa.accept_15_6_7_13_1_1666 36 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 253 (accept_3_3 35 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 253 (accept_3_3 32 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 253 (accept_3_3 29 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 253 (Polychromatic418967fa.accept_13_2_8_6_1_2390 28 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 253 (accept_3_3 26 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 253 (accept_3_3 23 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 253 (accept_3_3 20 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 253 (Polychromatic418967fa.accept_17_2_10_15_1_1238 19 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 253 (Polychromatic418967fa.accept_19_18_17_6_1_5775 18 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 253 (accept_3_3 17 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 112 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 253 (accept_3_3 14 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 253 (Polychromatic418967fa.accept_19_13_17_6_1_11363 13 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 253 (accept_3_3 11 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 112
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 253 (accept_3_3 8 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 253 (accept_3_3 5 112 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 253 (Polychromatic418967fa.accept_17_4_10_15_1_5444 4 112 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 253 (accept_3_3 2 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 112 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 253 (allA_succ_of_accept 110 111 253 (accept_3_3 110 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 253 (Polychromatic418967fa.accept_15_4_6_13_1_956 109 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 253
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 108 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 111 253 (accept_3_3 107 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 111 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 106 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 111 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 105 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 253 (accept_3_3 104 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 103 111
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 102 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 111 253 (accept_3_3 101 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 111 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 111 253 (Polychromatic418967fa.accept_16_3_15_13_1_2825 99 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 253 (accept_3_3 98 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 97 111 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 96 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 111 253 (accept_3_3 95 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 111 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 111 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 253 (accept_3_3 92 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 253 (Polychromatic418967fa.accept_14_7_13_1_1_922 91 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 90 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 111 253 (accept_3_3 89 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 111 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 111 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 253 (accept_3_3 86 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 85 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 253
  (Polychromatic418967fa.accept_18_12_3_1_1_3685 84 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 111 253 (accept_3_3 83 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 111 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 111 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 81 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 253 (accept_3_3 80 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 111 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 253 (accept_3_3 77 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 111 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 253 (accept_3_3 74 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 253 (Polychromatic418967fa.accept_22_7_1_11_1_10719 73 111 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 253
  (Polychromatic418967fa.accept_7_2_6_1_1_73 72 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 111 253 (accept_3_3 71 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 111 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 111 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 253 (accept_3_3 68 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 253 (accept_3_3 65 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 111 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 253 (Polychromatic418967fa.accept_14_7_13_1_1_922 63 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 253 (accept_3_3 62 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 111 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 111 253 (accept_3_3 59 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 111 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 111 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 57 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 253 (accept_3_3 56 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 253 (Polychromatic418967fa.accept_20_15_11_13_1_11192 55
  111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 253 (accept_3_3 53 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 111 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 253 (accept_3_3 50 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 253
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 253 (accept_3_3 47 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 253 (accept_3_3 44 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 111 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 253 (accept_3_3 41 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 253 (Polychromatic418967fa.accept_25_14_11_3_1_11835 39 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 253 (accept_3_3 38 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 111 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 253
  (Polychromatic418967fa.accept_21_15_6_1_1_6306 36 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 253 (accept_3_3 35 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 253 (accept_3_3 32 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 253 (accept_3_3 29 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 253 (Polychromatic418967fa.accept_13_1_7_6_1_142 27 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 253 (accept_3_3 26 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 111 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 253 (accept_3_3 23 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 253 (accept_3_3 20 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 111 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 253 (accept_3_3 17 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 253 (accept_3_3 14 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 253 (accept_3_3 11 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 253 (accept_3_3 8 111 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 253 (accept_3_3 5 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 253 (Polychromatic418967fa.accept_16_3_15_13_1_2825 3 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 253 (accept_3_3 2 111 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 253 (Polychromatic418967fa.accept_13_1_7_6_1_142 1 111 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 253 (allA_of_3_1 110 110 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 253
  (allA_succ_of_accept 108 109 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 108 109 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 253 (accept_3_3 107 109 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 109 253 (Polychromatic418967fa.accept_10_6_9_3_1_935 106 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 253
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 105 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 253 (accept_3_3 104 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 103 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 109 253 (Polychromatic418967fa.accept_13_11_5_6_1_519 102 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 253 (accept_3_3 101 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 253 (Polychromatic418967fa.accept_15_10_4_13_1_4506 100
  109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 109 253
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 99 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 109 253 (accept_3_3 98 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 109 253 (Polychromatic418967fa.accept_21_13_4_1_1_942 97 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 109 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 96 109 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 109 253 (accept_3_3 95 109 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 109 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 94 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 109 253
  (Polychromatic418967fa.accept_25_18_9_3_1_15437 93 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 109 253 (accept_3_3 92 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 109 253 (Polychromatic418967fa.accept_21_7_4_1_1_3300 91 109 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 109 253 (Polychromatic418967fa.accept_13_12_5_6_1_1050 90 109
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 109 253 (accept_3_3 89 109
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 109 253
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 88 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 109 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 109 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 109 253 (accept_3_3 86 109 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 109 253 (Polychromatic418967fa.accept_15_10_4_13_1_4506 85 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 109 253
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 109 253 (accept_3_3 83 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 109 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 82 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 109 253 (Polychromatic418967fa.accept_13_3_5_6_1_3192 81 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 109 253 (accept_3_3 80 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 109 253 (Polychromatic418967fa.accept_13_1_5_6_1_1048 79 109
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 109 253
  (Polychromatic418967fa.accept_22_12_21_11_1_12243 78 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 109 253 (accept_3_3 77 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 109 253 (Polychromatic418967fa.accept_10_6_9_3_1_935 76 109 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 109 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 109 253 (accept_3_3 74 109 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 109 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 73
  109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 109 253
  (Polychromatic418967fa.accept_27_18_1_10_1_11658 72 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 109 253 (accept_3_3 71 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 109 253 (Polychromatic418967fa.accept_15_10_4_13_1_4506 70 109 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 253 (Polychromatic418967fa.accept_13_4_5_6_1_3201
  69 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 253 (accept_3_3 68
  109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 109 253
  (Polychromatic418967fa.accept_19_10_14_6_1_5819 67 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 109 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 253 (accept_3_3 65 109 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 253 (Polychromatic418967fa.accept_10_4_9_3_1_1907 64 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 253
  (Polychromatic418967fa.accept_13_11_5_6_1_519 63 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 253 (accept_3_3 62 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 253 (Polychromatic418967fa.accept_14_4_11_1_1_940 60 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 253 (accept_3_3 59 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 253 (Polychromatic418967fa.accept_19_1_14_6_1_1983 58 109
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 253
  (Polychromatic418967fa.accept_25_7_9_3_1_15436 57 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 253 (accept_3_3 56 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 253 (Polychromatic418967fa.accept_13_3_5_6_1_3192 55 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 109 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 253 (accept_3_3 53 109 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 253
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 51 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 253 (accept_3_3 50 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 253 (Polychromatic418967fa.accept_13_10_5_6_1_1671 49 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 253 (Polychromatic418967fa.accept_19_10_14_6_1_5819 48 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 253 (accept_3_3 47 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 253 (Polychromatic418967fa.accept_10_6_9_3_1_935 46 109
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 253 (accept_3_3 44 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 253 (Polychromatic418967fa.accept_13_4_5_6_1_3201 43 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 253 (Polychromatic418967fa.accept_13_3_5_6_1_3192 42 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 253 (accept_3_3 41 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 109 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 253
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 39 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 253 (accept_3_3 38 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 253 (Polychromatic418967fa.accept_13_11_5_6_1_519 37 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 253 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 253 (accept_3_3 35 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 253 (Polychromatic418967fa.accept_10_4_9_3_1_1907 34 109
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 253 (accept_3_3 32 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 253 (Polychromatic418967fa.accept_13_4_5_6_1_3201 30 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 253 (accept_3_3 29 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 253 (Polychromatic418967fa.accept_19_9_14_6_1_2014 28 109
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 253
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 253 (accept_3_3 26 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 253 (Polychromatic418967fa.accept_13_12_5_6_1_1050 25 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 109 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 253 (accept_3_3 23 109 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 253 (Polychromatic418967fa.accept_17_5_7_15_1_1230 22 109 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 253
  (Polychromatic418967fa.accept_15_6_4_13_1_403 21 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 253 (accept_3_3 20 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 253 (Polychromatic418967fa.accept_14_4_11_1_1_940 18 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 253 (accept_3_3 17 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 253 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 109
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 253
  (Polychromatic418967fa.accept_22_15_21_11_1_15435 15 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 109 253 (accept_3_3 14 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 109 253 (Polychromatic418967fa.accept_21_13_4_1_1_942 13 109 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 109 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 253 (accept_3_3 11 109 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 10
  109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 253
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 253 (accept_3_3 8 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 253 (Polychromatic418967fa.accept_19_7_14_6_1_9987 7 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 253 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 109 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 253 (accept_3_3 5 109 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 253 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 109 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 253 (accept_3_3 2 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 253 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 109 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 253 (allA_succ_of_accept 107 108 253 (accept_3_3 107 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 108 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 106 108 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 108 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 105 108
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 253 (accept_3_3 104 108
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 108 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 103 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 108 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 102 108 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 253 (accept_3_3 101 108 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 108 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 100 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 253
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 99 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 108 253 (accept_3_3 98 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 108 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 97 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 108 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 108 253 (accept_3_3 95 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 253 (Polychromatic418967fa.accept_17_9_6_15_1_5454 94 108 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 253
  (Polychromatic418967fa.accept_7_2_3_1_1_10 93 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 108 253 (accept_3_3 92 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 108 253 (Polychromatic418967fa.accept_10_1_8_3_1_947 91 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 108 253 (Polychromatic418967fa.accept_16_10_12_13_1_4950 90 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 108 253 (accept_3_3 89 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 88 108 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 253
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 87 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 108 253 (accept_3_3 86 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 108 253 (Polychromatic418967fa.accept_10_5_8_3_1_229 85 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 108 253 (Polychromatic418967fa.accept_15_9_3_13_1_1686 84 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 108 253 (accept_3_3 83 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 82 108 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 108 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 108 253 (accept_3_3 80 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 108 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 108 253 (Polychromatic418967fa.accept_19_2_13_6_1_1978 78 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 108 253 (accept_3_3 77 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 76 108
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 108 253 (accept_3_3 74 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 108 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 108 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 108 253 (accept_3_3 71 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 253 (Polychromatic418967fa.accept_13_5_4_6_1_2371 70 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 253
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 69 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 108 253 (accept_3_3 68 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 108 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 108 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 66 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 108 253 (accept_3_3 65 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 253 (Polychromatic418967fa.accept_19_7_13_6_1_1914 64 108
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 253
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 63 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 108 253 (accept_3_3 62 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 108 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 108 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 108 253 (accept_3_3 59 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 253
  (Polychromatic418967fa.accept_8_1_4_5_1_48 57 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 108 253 (accept_3_3 56 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 108 253 (Polychromatic418967fa.accept_10_5_8_3_1_229 55 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 108 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 108 253 (accept_3_3 53 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 253 (Polychromatic418967fa.accept_16_4_12_13_1_990 52 108 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 253
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 108 253 (accept_3_3 50 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 108 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 108 253 (Polychromatic418967fa.accept_13_9_4_6_1_1005 48 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 108 253 (accept_3_3 47 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 108 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 253
  (Polychromatic418967fa.accept_10_5_8_3_1_229 45 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 108 253 (accept_3_3 44 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 108 253 (Polychromatic418967fa.accept_17_9_6_15_1_5454 43 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 108 253 (Polychromatic418967fa.accept_15_12_3_13_1_4481 42 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 253 (accept_3_3 41 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 108 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 108 253 (accept_3_3 38 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 108 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 108 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 253 (accept_3_3 35 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 253 (Polychromatic418967fa.accept_19_15_13_6_1_8636 34 108
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 108 253 (accept_3_3 32 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 108 253 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 108 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 253 (accept_3_3 29 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 253 (Polychromatic418967fa.accept_13_2_4_6_1_2356 28 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 253
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 27 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 108 253 (accept_3_3 26 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 108 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 108 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 253 (Polychromatic418967fa.accept_13_11_4_6_1_1006 24 108
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 253 (accept_3_3 23 108
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 253
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 22 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 108 253 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 108 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 253 (accept_3_3 20 108 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 108 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 18
  108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 253 (accept_3_3 17
  108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 253
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 108 253 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 108 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 253 (accept_3_3 14 108 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 108 253 (Polychromatic418967fa.accept_22_13_20_11_1_10762 13 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 108 253 (accept_3_3 11 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 108 253 (Polychromatic418967fa.accept_13_10_4_6_1_3224 10 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 108 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 253 (accept_3_3 8 108 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 253 (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 253
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 108 253 (accept_3_3 5 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  108 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 108 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 108 253 (Polychromatic418967fa.accept_20_3_8_13_1_3832 3 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 253 (accept_3_3 2 108 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 108 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 253 (allA_of_3_1 107 107 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 253
  (allA_succ_of_accept 105 106 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 105 106 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 106 253 (accept_3_3 104 106 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 106 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 102 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 106 253 (accept_3_3 101 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 106 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 100 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 106 253 (accept_3_3 98 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 106 253 (Polychromatic418967fa.accept_10_7_6_3_1_927 97 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 106 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 96 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 106 253 (accept_3_3 95 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 106 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 94 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 106 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 106 253 (accept_3_3 92 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 106 253
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 90 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 106 253 (accept_3_3 89 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 106 253 (Polychromatic418967fa.accept_10_8_6_3_1_1394 88 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 253 (accept_3_3 86 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 84 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 253 (accept_3_3 83 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 253 (Polychromatic418967fa.accept_13_4_2_6_1_1043 82 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 253 (accept_3_3 80 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 106 253 (accept_3_3 77 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 106 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 253 (accept_3_3 74 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 253 (Polychromatic418967fa.accept_13_8_2_6_1_2385 73 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 253
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 72 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 253 (accept_3_3 71 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 253 (Polychromatic418967fa.accept_15_10_1_13_1_2609 70 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 253 (accept_3_3 68 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 253 (accept_3_3 65 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 253 (accept_3_3 62 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 253 (Polychromatic418967fa.accept_13_9_2_6_1_514 61 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 253 (accept_3_3 59 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 253 (accept_3_3 56 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 253
  (Polychromatic418967fa.accept_19_16_11_6_1_7149 54 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 106 253 (accept_3_3 53 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 106 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 106 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 106 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 253 (accept_3_3 50 106 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 253 (Polychromatic418967fa.accept_9_4_7_1_1_379
  49 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 253 (accept_3_3 47 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 253 (Polychromatic418967fa.accept_16_14_10_13_1_2768 46 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 106 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 253 (accept_3_3 44 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 106 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 253 (accept_3_3 41 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 253 (accept_3_3 38 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 253 (Polychromatic418967fa.accept_10_7_6_3_1_927 37 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 253
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 106 253 (accept_3_3 35 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 253 (Polychromatic418967fa.accept_13_8_2_6_1_2385 34 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 106 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 253 (accept_3_3 32 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 253 (accept_3_3 29 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 253 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 253 (accept_3_3 26 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 253 (Polychromatic418967fa.accept_13_12_2_6_1_2396 25 106 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 253 (accept_3_3 23 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 253 (accept_3_3 20 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 253
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 253 (accept_3_3 17 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 253 (accept_3_3 14 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 253 (accept_3_3 11 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 253 (Polychromatic418967fa.accept_13_10_2_6_1_1044 10 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 253 (accept_3_3 8 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 253 (accept_3_3 5 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 106 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 253 (accept_3_3 2 106 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 253 (Polychromatic418967fa.accept_13_1_2_6_1_515 1 106 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 253 (allA_succ_of_accept 104 105 253 (accept_3_3 104 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 103 105 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 102 105
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 253 (accept_3_3 101 105
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 105 253
  (Polychromatic418967fa.accept_6_4_3_1_1_57 100 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 105 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 99 105 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 105 253 (accept_3_3 98 105 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 105 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 97 105 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 253 (Polychromatic418967fa.accept_13_5_1_6_1_2367
  96 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 253 (accept_3_3 95
  105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 105 253
  (Polychromatic418967fa.accept_6_4_3_1_1_57 94 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 105 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 105 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 253 (accept_3_3 92 105 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 105 253 (Polychromatic418967fa.accept_19_15_10_6_1_7169 91 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 253
  (Polychromatic418967fa.accept_14_6_7_1_1_78 90 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 105 253 (accept_3_3 89 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 105 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 87 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 253 (accept_3_3 86 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 85 105 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 253
  (Polychromatic418967fa.accept_8_4_1_5_1_186 84 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 105 253 (accept_3_3 83 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 105 253 (Polychromatic418967fa.accept_13_3_1_6_1_509 81 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 253 (accept_3_3 80 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 79 105 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 253
  (Polychromatic418967fa.accept_10_8_5_3_1_543 78 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 105 253 (accept_3_3 77 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 105 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 105 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 253 (accept_3_3 74 105 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 253 (Polychromatic418967fa.accept_13_8_1_6_1_997 73 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 253
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 105 253 (accept_3_3 71 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 105 253 (Polychromatic418967fa.accept_14_13_7_1_1_1618 69 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 253 (accept_3_3 68 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 105 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 105 253 (accept_3_3 65 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 105 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 63 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 253 (accept_3_3 62 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 105 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 253
  (Polychromatic418967fa.accept_8_4_1_5_1_186 60 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 105 253 (accept_3_3 59 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 105 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 253 (accept_3_3 56 105 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 253 (Polychromatic418967fa.accept_13_3_1_6_1_509 55 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 253
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 54 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 253 (accept_3_3 53 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 51 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 253 (accept_3_3 50 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 105 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 253 (accept_3_3 47 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 253 (Polychromatic418967fa.accept_25_20_5_3_1_15434 45 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 253 (accept_3_3 44 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 105 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 253
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 253 (accept_3_3 41 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 105 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 253 (accept_3_3 38 105 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 253
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 253 (accept_3_3 35 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 253 (Polychromatic418967fa.accept_13_7_1_6_1_3287 33 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 253 (accept_3_3 32 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 105 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 253 (accept_3_3 29 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 253 (accept_3_3 26 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 105 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 253
  (Polychromatic418967fa.accept_22_2_17_11_1_15433 24 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 253 (accept_3_3 23 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 105 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 105 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 253 (accept_3_3 20 105 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 253
  (Polychromatic418967fa.accept_20_19_5_13_1_2593 19 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 105 253 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 253 (accept_3_3 17 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 253
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 105 253 (accept_3_3 14 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 105 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 105 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 105 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 253 (accept_3_3 11 105 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 253
  (Polychromatic418967fa.accept_13_9_1_6_1_510 9 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 253 (accept_3_3 8 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  105 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 253 (Polychromatic418967fa.accept_14_6_7_1_1_78 6 105 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 253 (accept_3_3 5 105 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 253 (accept_3_3 2 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 253 (Polychromatic418967fa.accept_16_1_9_13_1_1822 1 105 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 253 (allA_of_3_1 104 104 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 253
  (allA_succ_of_accept 102 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 103 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 253 (accept_3_3 101 103 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 253 (Polychromatic418967fa.accept_16_4_7_13_1_2795 100 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 253
  (Polychromatic418967fa.accept_21_15_19_1_1_12505 99 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 103 253 (accept_3_3 98 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 103 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 97 103 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 103 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 96 103 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 253 (accept_3_3 95 103 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 94
  103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 93 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 253 (accept_3_3 92 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 253 (Polychromatic418967fa.accept_20_11_3_13_1_6745 91 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 253 (accept_3_3 89 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 88 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 87 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 253 (accept_3_3 86 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 253 (Polychromatic418967fa.accept_13_7_12_6_1_1039 85 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 253 (accept_3_3 83 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 81 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 253 (accept_3_3 80 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 253 (accept_3_3 77 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 75 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 253 (accept_3_3 74 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 253 (Polychromatic418967fa.accept_13_7_12_6_1_1039 72 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 253 (accept_3_3 71 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 103 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 253 (accept_3_3 68 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 253 (accept_3_3 65 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 253 (Polychromatic418967fa.accept_18_10_13_1_1_7736 64 103 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 253
  (Polychromatic418967fa.accept_17_12_1_15_1_5472 63 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 103 253 (accept_3_3 62 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 103 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 103 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 103 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 253 (accept_3_3 59 103 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 58
  103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 253 (accept_3_3 56 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 253 (accept_3_3 53 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 253 (accept_3_3 50 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 253 (Polychromatic418967fa.accept_13_10_12_6_1_991 49 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 253 (accept_3_3 47 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 253 (accept_3_3 44 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 253 (accept_3_3 41 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 253 (Polychromatic418967fa.accept_19_2_8_6_1_1905 40 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 253 (accept_3_3 38 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 253 (Polychromatic418967fa.accept_17_3_1_15_1_6835 37 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 253 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 253 (accept_3_3 35 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 103 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 253 (accept_3_3 32 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 253 (accept_3_3 29 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 253 (Polychromatic418967fa.accept_13_2_12_6_1_2394 28 103 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 253 (accept_3_3 26 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 253 (accept_3_3 23 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 253 (accept_3_3 20 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 253 (Polychromatic418967fa.accept_24_19_7_13_1_10414 19 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 253 (accept_3_3 17 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 103 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 253 (accept_3_3 14 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 253 (accept_3_3 11 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 253
  (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 253 (accept_3_3 8 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 253 (accept_3_3 5 103 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 103 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 253 (accept_3_3 2 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 253 (Polychromatic418967fa.accept_20_1_3_13_1_8217 1 103 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 253 (allA_succ_of_accept 101 102 253 (accept_3_3 101 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 102 253 (Polychromatic418967fa.accept_15_10_12_13_1_2585 100 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 99
  102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 253 (accept_3_3 98
  102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 253
  (Polychromatic418967fa.accept_9_7_3_1_1_386 97 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 102 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 96 102 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 102 253 (accept_3_3 95 102 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 102 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 94 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 102 253
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 93 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 102 253 (accept_3_3 92 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 102 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 253 (Polychromatic418967fa.accept_19_14_7_6_1_8654 90 102
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 102 253 (accept_3_3 89 102
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 102 253
  (Polychromatic418967fa.accept_9_7_3_1_1_386 88 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 102 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 102 253 (accept_3_3 86 102 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 102 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 85 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 253
  (Polychromatic418967fa.accept_16_4_6_13_1_1874 84 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 102 253 (accept_3_3 83 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 102 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 82 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 102 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 81 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 102 253 (accept_3_3 80 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 102 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 102 253 (accept_3_3 77 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 102 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 102 253 (accept_3_3 74 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 253
  (Polychromatic418967fa.accept_21_9_18_1_1_9424 72 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 102 253 (accept_3_3 71 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 102 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 102 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 253 (accept_3_3 68 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 66 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 102 253 (accept_3_3 65 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 102 253 (Polychromatic418967fa.accept_22_20_14_11_1_12258 64 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 253 (accept_3_3 62 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 102 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 253 (accept_3_3 59 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 102 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 253 (Polychromatic418967fa.accept_13_5_11_6_1_505 57 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 253 (accept_3_3 56 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 102 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 102 253 (accept_3_3 53 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 102 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 253 (accept_3_3 50 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 253
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 48 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 253 (accept_3_3 47 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 102 253 (Polychromatic418967fa.accept_15_1_12_13_1_944 46 102 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 102 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 253 (accept_3_3 44 102 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 102 253 (accept_3_3 41 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 102 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 253 (accept_3_3 38 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 253 (Polychromatic418967fa.accept_19_18_7_6_1_4367 37 102 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 253
  (Polychromatic418967fa.accept_16_4_6_13_1_1874 36 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 102 253 (accept_3_3 35 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 102 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 102 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 253 (accept_3_3 32 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 253
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 30 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 102 253 (accept_3_3 29 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 102 253 (Polychromatic418967fa.accept_26_2_24_19_1_15432 28 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 253 (accept_3_3 26 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 102 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 253 (accept_3_3 23 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 253 (accept_3_3 20 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 253
  (Polychromatic418967fa.accept_13_5_11_6_1_505 18 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 102 253 (accept_3_3 17 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 102 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 253 (accept_3_3 14 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 102 253 (accept_3_3 11 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 102 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 102 253 (Polychromatic418967fa.accept_16_9_6_13_1_3831 9 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 253 (accept_3_3 8 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 253 (accept_3_3 5 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 102 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 253 (accept_3_3 2 102 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 102 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 253 (allA_of_3_1 101 101 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 253 (allA_succ_of_accept 99
  100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 100 253 (accept_3_3 98 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 100 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 97 100 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 100 253 (Polychromatic418967fa.accept_19_1_5_6_1_5811 96 100
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 100 253 (accept_3_3 95 100
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 100 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 94 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 100 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 100 253 (accept_3_3 92 100 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 100 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 91 100 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 100 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 90 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 100 253 (accept_3_3 89 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 100 253 (Polychromatic418967fa.accept_13_10_9_6_1_1026 88 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 100 253 (accept_3_3 86 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 100 253 (Polychromatic418967fa.accept_13_7_9_6_1_148 85 100 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 100 253
  (Polychromatic418967fa.accept_22_18_12_11_1_5892 84 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 100 253 (accept_3_3 83 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 100 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 82 100 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 100 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 100 253 (accept_3_3 80 100 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 100 253 (Polychromatic418967fa.accept_13_1_9_6_1_146
  79 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 100 253
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 78 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 100 253 (accept_3_3 77 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 100 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 100 253 (accept_3_3 74 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 100 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 100 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 100 253
  (Polychromatic418967fa.accept_13_7_9_6_1_148 72 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 100 253 (accept_3_3 71 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 100 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 100 253 (accept_3_3 68 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 100 253 (Polychromatic418967fa.accept_13_2_9_6_1_501 67 100 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 100 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 66 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 100 253 (accept_3_3 65 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 100 253 (Polychromatic418967fa.accept_14_8_2_1_1_1652 64 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 100 253 (accept_3_3 62 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 100 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 61 100 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 100 253
  (Polychromatic418967fa.accept_16_12_4_13_1_3827 60 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 100 253 (accept_3_3 59 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 100 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 100 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 100 253 (accept_3_3 56 100 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 100 253 (Polychromatic418967fa.accept_7_6_2_1_1_214
  55 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 100 253
  (Polychromatic418967fa.accept_13_2_9_6_1_501 54 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 100 253 (accept_3_3 53 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 100 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 100 253 (accept_3_3 50 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 100 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 100 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 100 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 100 253 (accept_3_3 47 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 100 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 100 253 (accept_3_3 44 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 100 253 (Polychromatic418967fa.accept_13_4_9_6_1_2376 43 100 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 100 253
  (Polychromatic418967fa.accept_13_3_9_6_1_502 42 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 100 253 (accept_3_3 41 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 100 253 (Polychromatic418967fa.accept_13_1_9_6_1_146 40 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 100 253 (accept_3_3 38 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 100 253 (Polychromatic418967fa.accept_19_18_5_6_1_2004 37 100 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 253
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 100 253 (accept_3_3 35 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 100 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 253 (accept_3_3 32 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 100 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 100 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 100 253
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 30 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 100 253 (accept_3_3 29 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 100 253 (Polychromatic418967fa.accept_13_2_9_6_1_501 28 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 100 253 (accept_3_3 26 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 100 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 100 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 100 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 100 253 (accept_3_3 23 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 100 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 100 253 (accept_3_3 20 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 100 253 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 100 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 100 253
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 100 253 (accept_3_3 17 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 100 253 (Polychromatic418967fa.accept_13_3_9_6_1_502 16 100 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 100 253 (accept_3_3 14 100 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 253 (Polychromatic418967fa.accept_7_6_2_1_1_214
  13 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 253
  (Polychromatic418967fa.accept_15_12_10_13_1_4497 12 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 100 253 (accept_3_3 11 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 100 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 100 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 253 (accept_3_3 8 100 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 100 253 (Polychromatic418967fa.accept_13_7_9_6_1_148 7
  100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 100 253 (accept_3_3 5 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  100 253 (Polychromatic418967fa.accept_13_4_9_6_1_2376 4 100 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 100 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 253 (accept_3_3 2 100 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 100 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 99
  253 (allA_succ_of_accept 98 99 253 (accept_3_3 98 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 99 253 (Polychromatic418967fa.accept_15_7_9_13_1_3451 97 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 99 253 (Polychromatic418967fa.accept_10_6_9_3_1_935 96 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 253 (accept_3_3 95 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 253
  (Polychromatic418967fa.accept_12_9_3_1_1_303 93 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 253 (accept_3_3 92 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 253 (Polychromatic418967fa.accept_17_6_14_15_1_5505 91 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 253 (accept_3_3 89 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 88 99 253 11 8 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 99 253 (Polychromatic418967fa.accept_21_3_15_1_1_2046 87 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 253 (accept_3_3 86 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 253 (Polychromatic418967fa.accept_20_5_19_13_1_6717 85 99
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 99 253
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 99 253 (accept_3_3 83 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  99 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 99 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 81 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 253 (accept_3_3 80 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 253 (Polychromatic418967fa.accept_13_1_8_6_1_1016 79 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 99 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 99 253 11 7 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 76 99 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 99 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 253 (Polychromatic418967fa.accept_18_3_9_1_1_3690 75 99 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 253 (accept_3_3 74 99 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 253
  (Polychromatic418967fa.accept_21_10_15_1_1_9494 73 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 99 253 (Polychromatic418967fa.accept_16_8_3_13_1_7295 72 99 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 253 (accept_3_3 71 99 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 99 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 253 (Polychromatic418967fa.accept_12_9_3_1_1_303
  69 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 253 (accept_3_3 68
  99 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 253
  (Polychromatic418967fa.accept_13_2_8_6_1_2390 67 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 99 253 11 6 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 99 253 (accept_3_3 65 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  99 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 99 253 (Polychromatic418967fa.accept_13_11_8_6_1_1023 63 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 253 (accept_3_3 62 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 253 (Polychromatic418967fa.accept_21_19_15_1_1_6345 61 99
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 99 253
  (Polychromatic418967fa.accept_18_6_9_1_1_3769 60 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 99 253 (accept_3_3 59 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  99 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 99 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 57 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 253 (accept_3_3 56 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 55 99 253 11 5 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 99 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 253 (accept_3_3 53 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 253
  (Polychromatic418967fa.accept_19_13_4_6_1_9960 51 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 253 (accept_3_3 50 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 253 (Polychromatic418967fa.accept_15_4_9_13_1_2582 49 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 253 (Polychromatic418967fa.accept_15_3_9_13_1_1681 48 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 253 (accept_3_3 47 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 253
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 99 253 11 4 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 99 253 (Polychromatic418967fa.accept_19_5_4_6_1_11375 43 99 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 253 (accept_3_3 41 99 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40
  99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 253
  (Polychromatic418967fa.accept_18_3_9_1_1_3690 39 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 253 (accept_3_3 38 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 253 (Polychromatic418967fa.accept_13_11_8_6_1_1023 37 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 253 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 253 (accept_3_3 35 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99 253 11 3 9 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 99 253 (accept_3_3 32 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 253 (Polychromatic418967fa.accept_16_15_3_13_1_2818 31 99
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 99 253 (accept_3_3 29 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  99 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 99 253 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 253 (accept_3_3 26 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 253 (Polychromatic418967fa.accept_20_5_19_13_1_6717 25 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 253
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 99 253 (accept_3_3 23 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 99
  253 11 2 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  99 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 253 (accept_3_3 20 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 253 (Polychromatic418967fa.accept_15_4_9_13_1_2582 19 99 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 253 (accept_3_3 17 99 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 253
  (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 253 (accept_3_3 14 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 253 (Polychromatic418967fa.accept_19_13_4_6_1_9960 13 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 253 (Polychromatic418967fa.accept_17_12_14_15_1_5561 12 99 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 99 253 11 1 9 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 99 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 99 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 99 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 253 (accept_3_3 8 99 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 99 253 (Polychromatic418967fa.accept_15_7_9_13_1_3451 7 99 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 253 (accept_3_3 5 99 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 253
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 253 (accept_3_3 2 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  253 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 99 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  253 (allA_of_3_1 98 98 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 253 (allA_succ_of_accept 96 97 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 96 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 253 (accept_3_3 95 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 94 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 253 (accept_3_3 92 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 253 (Polychromatic418967fa.accept_14_7_13_1_1_922 91 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 253
  (Polychromatic418967fa.accept_20_10_17_13_1_6773 90 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 97 253 (accept_3_3 89 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 97 253 (Polychromatic418967fa.accept_17_3_12_15_1_1203 88 97 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 87 97 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 253 (accept_3_3 86 97 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 85
  97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 253
  (Polychromatic418967fa.accept_8_4_1_5_1_186 84 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 253 (accept_3_3 83 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 82 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 253 (Polychromatic418967fa.accept_15_6_7_13_1_1666 81 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 253 (accept_3_3 80 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 79 97 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 253 (accept_3_3 77 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 76 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 253 (accept_3_3 74 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 253 (Polychromatic418967fa.accept_16_9_1_13_1_1850 73 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 253
  (Polychromatic418967fa.accept_7_2_6_1_1_73 72 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 253 (accept_3_3 71 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 253 (Polychromatic418967fa.accept_18_16_7_1_1_6332 70 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 253 (accept_3_3 68 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 253 (accept_3_3 65 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 253 (Polychromatic418967fa.accept_10_4_7_3_1_54 64 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 253 (Polychromatic418967fa.accept_14_7_13_1_1_922 63 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 253 (accept_3_3 62 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 253
  (Polychromatic418967fa.accept_8_4_1_5_1_186 60 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 253 (accept_3_3 59 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 253 (accept_3_3 56 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 253 (accept_3_3 53 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 253 (accept_3_3 50 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 253 (accept_3_3 47 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 253 (Polychromatic418967fa.accept_10_6_7_3_1_547 46 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 253 (accept_3_3 44 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 253 (Polychromatic418967fa.accept_24_19_1_13_1_10411 43 97 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 253 (accept_3_3 41 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 253 (accept_3_3 38 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 253
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 253 (accept_3_3 35 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 253 (Polychromatic418967fa.accept_10_4_7_3_1_54 34 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 253 (accept_3_3 32 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 253
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 253 (accept_3_3 29 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 253 (Polychromatic418967fa.accept_19_8_2_6_1_8677 27 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 253 (accept_3_3 26 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 253 (accept_3_3 23 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 253 (accept_3_3 20 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 253
  (Polychromatic418967fa.accept_17_1_12_15_1_1263 18 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 253 (accept_3_3 17 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 253 (accept_3_3 14 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 253 (accept_3_3 11 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 253 (Polychromatic418967fa.accept_19_10_2_6_1_5731 10 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 253 (accept_3_3 8 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 253 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 97 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 253 (accept_3_3 5 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  253 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 97 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 97 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 253 (accept_3_3 2 97 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 253 (Polychromatic418967fa.accept_17_1_12_15_1_1263 1 97 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 253
  (allA_succ_of_accept 95 96 253 (accept_3_3 95 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  96 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 94 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 96 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 96 253 (accept_3_3 92 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 253 (Polychromatic418967fa.accept_21_7_12_1_1_952 91 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 90 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 96 253 (accept_3_3 89 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  96 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 88 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 96 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 96 253 (accept_3_3 86 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 85 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 96 253 (accept_3_3 83 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  96 253 (Polychromatic418967fa.accept_13_4_5_6_1_3201 82 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 96 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 96 253 (accept_3_3 80 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 79 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 253
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 78 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 96 253 (accept_3_3 77 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  96 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 96 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 253 (accept_3_3 74 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 253
  (Polychromatic418967fa.accept_17_4_11_15_1_3170 72 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 253 (accept_3_3 71 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  96 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 253 (accept_3_3 68 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 253 (accept_3_3 65 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  96 253 (Polychromatic418967fa.accept_13_12_5_6_1_1050 64 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 253 (Polychromatic418967fa.accept_13_11_5_6_1_519 63 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 253 (accept_3_3 62 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 253 (accept_3_3 59 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 253 (accept_3_3 56 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 253
  (Polychromatic418967fa.accept_22_10_8_11_1_10756 54 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 96 253 (accept_3_3 53 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 96 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 96 253 (Polychromatic418967fa.accept_13_12_5_6_1_1050 51 96
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 253 (accept_3_3 50 96 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 49
  96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 253 (accept_3_3 47 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 253 (accept_3_3 44 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 253
  (Polychromatic418967fa.accept_13_3_5_6_1_3192 42 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 253 (accept_3_3 41 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 253 (accept_3_3 38 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 253 (Polychromatic418967fa.accept_10_7_6_3_1_927 37 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 253
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 253 (accept_3_3 35 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 253 (Polychromatic418967fa.accept_17_16_11_15_1_4353 33 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 253 (accept_3_3 32 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 96 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 253 (accept_3_3 29 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 253 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 253 (accept_3_3 26 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 253 (accept_3_3 23 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 253 (accept_3_3 20 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 253 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 253 (accept_3_3 17 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 253 (Polychromatic418967fa.accept_21_15_12_1_1_9491 15 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 253 (accept_3_3 14 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 96 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 253 (accept_3_3 11 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 253 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 253 (accept_3_3 8 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 253 (accept_3_3 5 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  253 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 96 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 96 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 253 (accept_3_3 2 96 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 253 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 96 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 253
  (allA_of_3_1 95 95 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 253 (allA_succ_of_accept 93 94 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 94 253 (accept_3_3 92 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  94 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 94 253 (Polychromatic418967fa.accept_16_10_14_13_1_1870 90 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 253 (accept_3_3 89 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 88 94 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 94 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 94 253 (accept_3_3 86 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  94 253 (Polychromatic418967fa.accept_15_10_4_13_1_4506 85 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 94 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 253 (accept_3_3 83 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 82 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 253 (accept_3_3 80 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 78 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 253 (accept_3_3 77 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 76 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 253 (accept_3_3 74 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 253 (Polychromatic418967fa.accept_22_7_6_11_1_13808 73 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 253 (accept_3_3 71 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 253 (accept_3_3 68 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 253 (accept_3_3 65 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 253 (accept_3_3 62 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 253 (accept_3_3 59 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 253 (accept_3_3 56 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 253 (accept_3_3 53 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 253 (accept_3_3 50 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 253 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 253 (accept_3_3 47 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 253 (accept_3_3 44 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 253 (accept_3_3 41 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 253 (accept_3_3 38 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 253 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 253 (accept_3_3 35 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 94 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 253 (accept_3_3 32 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 253 (accept_3_3 29 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 253 (accept_3_3 26 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 253 (accept_3_3 23 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 253 (Polychromatic418967fa.accept_13_9_3_6_1_1661 22 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 253 (accept_3_3 20 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 253 (accept_3_3 17 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 253 (accept_3_3 14 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 253 (Polychromatic418967fa.accept_21_13_10_1_1_6292 13 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 253 (accept_3_3 11 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 253 (Polychromatic418967fa.accept_13_10_3_6_1_1003 10 94 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 253 (accept_3_3 8 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 94 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 253 (accept_3_3 5 94 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 94 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 253 (accept_3_3 2 94 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 253 (Polychromatic418967fa.accept_13_1_3_6_1_158 1
  94 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 253
  (allA_succ_of_accept 92 93 253 (accept_3_3 92 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 253 (Polychromatic418967fa.accept_15_1_3_13_1_2548 91 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 253 (accept_3_3 89 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 253 (accept_3_3 86 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 85 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 253 (Polychromatic418967fa.accept_15_9_3_13_1_1686 84 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 253 (accept_3_3 83 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 93 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 253
  (Polychromatic418967fa.accept_17_13_8_15_1_8135 81 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 253 (accept_3_3 80 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 78 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 253 (accept_3_3 77 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 253
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 253 (accept_3_3 74 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 253 (Polychromatic418967fa.accept_15_12_3_13_1_4481 72 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 253 (accept_3_3 71 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 93 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 253 (accept_3_3 68 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 253 (accept_3_3 65 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 253
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 253 (accept_3_3 62 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 253 (accept_3_3 59 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 253
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 57 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 253 (accept_3_3 56 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 253 (Polychromatic418967fa.accept_15_9_3_13_1_1686 54 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 253 (accept_3_3 53 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 253 (accept_3_3 50 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 253 (accept_3_3 47 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 253 (accept_3_3 44 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 253 (accept_3_3 41 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 253
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 253 (accept_3_3 38 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 253 (Polychromatic418967fa.accept_19_18_17_6_1_5775 37 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 253 (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 253 (accept_3_3 35 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 93 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 253 (accept_3_3 32 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 253 (Polychromatic418967fa.accept_13_4_2_6_1_1043 30 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 253 (accept_3_3 29 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 253 (accept_3_3 26 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 253 (accept_3_3 23 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 253
  (Polychromatic418967fa.accept_13_8_2_6_1_2385 21 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 253 (accept_3_3 20 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 253 (Polychromatic418967fa.accept_25_19_18_3_1_15431 19 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 253 (Polychromatic418967fa.accept_19_18_17_6_1_5775 18 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 253 (accept_3_3 17 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 253 (accept_3_3 14 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 253 (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 253 (accept_3_3 11 93 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 93 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 253
  (Polychromatic418967fa.accept_13_9_2_6_1_514 9 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 253 (accept_3_3 8 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  253 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 93 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 253 (accept_3_3 5 93 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 253 (accept_3_3 2 93 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 253 (Polychromatic418967fa.accept_13_1_2_6_1_515 1
  93 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 253
  (allA_of_3_1 92 92 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 253 (allA_succ_of_accept 90 91 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 91 253 (accept_3_3 89 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  91 253 (Polychromatic418967fa.accept_10_8_1_3_1_1374 88 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 91 253 (Polychromatic418967fa.accept_15_12_1_13_1_3444 87 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 253 (accept_3_3 86 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 253 (Polychromatic418967fa.accept_15_10_1_13_1_2609 85 91
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 91 253
  (Polychromatic418967fa.accept_20_4_11_13_1_11184 84 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 91 253 (accept_3_3 83 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 91 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 253 (Polychromatic418967fa.accept_19_5_15_6_1_1986 81 91
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 253 (accept_3_3 80 91 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 253 (Polychromatic418967fa.accept_21_16_7_1_1_9430
  79 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 91 253 (accept_3_3 77 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  91 253 (Polychromatic418967fa.accept_14_6_7_1_1_78 76 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 91 253 (Polychromatic418967fa.accept_20_15_11_13_1_11192 75 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 253 (accept_3_3 74 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 253 (Polychromatic418967fa.accept_19_16_15_6_1_12661 73 91
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 253
  (Polychromatic418967fa.accept_10_2_1_3_1_233 72 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 253 (accept_3_3 71 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  91 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 91 253 (Polychromatic418967fa.accept_14_13_7_1_1_1618 69 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 253 (accept_3_3 68 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 253 (Polychromatic418967fa.accept_19_10_15_6_1_5772 67 91
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 253 (accept_3_3 65 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 253 (Polychromatic418967fa.accept_14_8_7_1_1_1615 64 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 91 253 (Polychromatic418967fa.accept_15_3_1_13_1_1672 63 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 253 (accept_3_3 62 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 253 (Polychromatic418967fa.accept_19_4_15_6_1_9954 61 91
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 253
  (Polychromatic418967fa.accept_17_9_6_15_1_5454 60 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 253 (accept_3_3 59 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 253 (Polychromatic418967fa.accept_15_12_1_13_1_3444 57 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 253 (accept_3_3 56 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 253 (Polychromatic418967fa.accept_14_13_7_1_1_1618 55 91
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 253 (accept_3_3 53 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 253 (Polychromatic418967fa.accept_10_2_1_3_1_233 52 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 253 (Polychromatic418967fa.accept_19_13_15_6_1_7131 51 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 253 (accept_3_3 50 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 253 (Polychromatic418967fa.accept_19_11_15_6_1_7173 49 91
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 253
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 253 (accept_3_3 47 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 253 (Polychromatic418967fa.accept_21_3_7_1_1_9521 45 91 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 253 (accept_3_3 44 91 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 253 (Polychromatic418967fa.accept_17_9_6_15_1_5454 43 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 253 (accept_3_3 41 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 253 (Polychromatic418967fa.accept_15_10_1_13_1_2609 40 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 253 (Polychromatic418967fa.accept_29_10_4_21_1_15430 39 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 253 (accept_3_3 38 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 253 (Polychromatic418967fa.accept_21_16_7_1_1_9430 37 91
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 253
  (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 253 (accept_3_3 35 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 253 (Polychromatic418967fa.accept_15_3_1_13_1_1672 33 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 253 (accept_3_3 32 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 253 (Polychromatic418967fa.accept_17_14_6_15_1_3151 31 91
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 253 (accept_3_3 29 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 253 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 253 (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 253 (accept_3_3 26 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 253 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 91
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 253
  (Polychromatic418967fa.accept_16_8_11_13_1_7265 24 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 253 (accept_3_3 23 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 253 (Polychromatic418967fa.accept_19_2_15_6_1_4408 21 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 253 (accept_3_3 20 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 253 (Polychromatic418967fa.accept_21_19_7_1_1_3329 19 91
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 253 (accept_3_3 17 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 253 (Polychromatic418967fa.accept_19_16_15_6_1_12661 16 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 253 (Polychromatic418967fa.accept_20_15_11_13_1_11192 15 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 253 (accept_3_3 14 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 253 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 91
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 253
  (Polychromatic418967fa.accept_10_2_1_3_1_233 12 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 253 (accept_3_3 11 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 253 (Polychromatic418967fa.accept_17_9_6_15_1_5454 9 91 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 253 (accept_3_3 8 91 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 253 (Polychromatic418967fa.accept_24_7_19_13_1_6703 7 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 253 (accept_3_3 5 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  253 (Polychromatic418967fa.accept_19_4_15_6_1_9954 4 91 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 253 (Polychromatic418967fa.accept_15_3_1_13_1_1672 3 91 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 253 (accept_3_3 2 91 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 253 (Polychromatic418967fa.accept_22_1_3_11_1_10754 1 91 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 253
  (allA_succ_of_accept 89 90 253 (accept_3_3 89 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  90 253 (Polychromatic418967fa.accept_13_10_12_6_1_991 88 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 90 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 90 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 90 253 (accept_3_3 86 90 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 253 (Polychromatic418967fa.accept_13_7_12_6_1_1039 85 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 253
  (Polychromatic418967fa.accept_19_8_14_6_1_5802 84 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 90 253 (accept_3_3 83 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  90 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 82 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 253 (Polychromatic418967fa.accept_17_13_5_15_1_8103 81 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 90 253 (accept_3_3 80 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 253
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 78 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 90 253 (accept_3_3 77 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 253 (Polychromatic418967fa.accept_16_12_10_13_1_1042 76 90 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 90 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 90 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 253 (accept_3_3 74 90 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 253
  (Polychromatic418967fa.accept_27_19_9_10_1_7747 73 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 90 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 90 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 253 (accept_3_3 71 90 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 90 253 (Polychromatic418967fa.accept_13_5_12_6_1_508 70 90 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 90 253
  (Polychromatic418967fa.accept_16_5_10_13_1_6042 69 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 90 253 (accept_3_3 68 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  90 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 90 253 (Polychromatic418967fa.accept_19_9_14_6_1_2014 66 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 90 253 (accept_3_3 65 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 253 (Polychromatic418967fa.accept_17_13_5_15_1_8103 64 90
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 90 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 90 253 (accept_3_3 62 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  90 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 90 253 (Polychromatic418967fa.accept_16_12_10_13_1_1042 60 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 253 (accept_3_3 59 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 90 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 90 253
  (Polychromatic418967fa.accept_13_5_12_6_1_508 57 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 90 253 (accept_3_3 56 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  90 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 90 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 90 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 253 (accept_3_3 53 90 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 253 (Polychromatic418967fa.accept_20_12_10_13_1_9747 52 90 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 90 253 (accept_3_3 50 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  90 253 (Polychromatic418967fa.accept_13_10_12_6_1_991 49 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 90 253 (Polychromatic418967fa.accept_19_10_14_6_1_5819 48 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 253 (accept_3_3 47 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 253 (Polychromatic418967fa.accept_13_7_12_6_1_1039 46 90
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 90 253
  (Polychromatic418967fa.accept_17_11_5_15_1_8144 45 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 90 253 (accept_3_3 44 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  90 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 90 253 (Polychromatic418967fa.accept_20_2_10_13_1_6766 42 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 253 (accept_3_3 41 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 90 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 90 253 (accept_3_3 38 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  90 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 90 253 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 253 (accept_3_3 35 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 253 (Polychromatic418967fa.accept_25_9_15_3_1_15429 34 90
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 90 253 (accept_3_3 32 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  90 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 90 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 90 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 253 (accept_3_3 29 90 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 253 (Polychromatic418967fa.accept_13_2_12_6_1_2394 28 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 90 253 (accept_3_3 26 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  90 253 (Polychromatic418967fa.accept_20_5_10_13_1_6754 25 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 90 253 (Polychromatic418967fa.accept_17_7_5_15_1_3184 24 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 253 (accept_3_3 23 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 253 (Polychromatic418967fa.accept_20_2_10_13_1_6766 22 90
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 253
  (Polychromatic418967fa.accept_14_7_6_1_1_1656 21 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 90 253 (accept_3_3 20 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  90 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 90 253 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 90 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 253 (accept_3_3 17 90 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 90 253 (accept_3_3 14 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  90 253 (Polychromatic418967fa.accept_17_13_5_15_1_8103 13 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 90 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 90 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 253 (accept_3_3 11 90 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 253 (Polychromatic418967fa.accept_13_10_12_6_1_991 10 90 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 90 253
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 253 (accept_3_3 8 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90
  253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 90 253 (Polychromatic418967fa.accept_22_6_2_11_1_13769 6 90 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 253 (accept_3_3 5 90 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 90 253 (Polychromatic418967fa.accept_25_4_15_3_1_15428 4 90 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 253 (accept_3_3 2 90 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 253 (Polychromatic418967fa.accept_19_1_14_6_1_1983
  1 90 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 253
  (allA_of_3_1 89 89 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 253 (allA_succ_of_accept 87 88 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 88 253 (accept_3_3 86 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  88 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 88 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 84 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 253 (accept_3_3 83 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 82 88 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 88 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 88 253 (accept_3_3 80 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  88 253 (Polychromatic418967fa.accept_18_7_16_1_1_4951 79 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 88 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 78 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 88 253 11 7 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 88 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 76
  88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 88 253 (accept_3_3 74 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  88 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 88 253 (Polychromatic418967fa.accept_19_15_12_6_1_8634 72 88 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 253 (accept_3_3 71 88 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 88
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 88 253 (accept_3_3 68 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  88 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 88 253 11 6 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 88 253 (accept_3_3 65 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 88 253 (Polychromatic418967fa.accept_13_12_10_6_1_3212 64 88 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 88 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 253 (accept_3_3 62 88 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 61
  88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 253 (accept_3_3 59 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 253 (accept_3_3 56 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 55 88 253 11 5 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 88 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 88 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 253 (accept_3_3 53 88 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 88 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 253 (accept_3_3 50 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 253 (accept_3_3 47 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 46 88 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 88 253 11 4 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 88 253 (Polychromatic418967fa.accept_13_4_10_6_1_989 43 88 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 88 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 253 (accept_3_3 41 88 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 40
  88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 253 (accept_3_3 38 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 253 (Polychromatic418967fa.accept_16_5_8_13_1_2764 37 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 253 (accept_3_3 35 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 88 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 88 253 11 3 8 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 88 253 (accept_3_3 32 88 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 88 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 253 (accept_3_3 29 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 253 (Polychromatic418967fa.accept_13_2_10_6_1_1676 28 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 253 (accept_3_3 26 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 253 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 88 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 253 (accept_3_3 23 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88
  253 11 2 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  88 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 88 253 (accept_3_3 20 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 88 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 88 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 253 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 88
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 253 (accept_3_3 17 88 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 253 (Polychromatic418967fa.accept_10_6_8_3_1_930
  16 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 253 (accept_3_3 14 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 88 253 11 1 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 88 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 10
  88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 253 (accept_3_3 8 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  253 (Polychromatic418967fa.accept_18_7_16_1_1_4951 7 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 88 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 253 (accept_3_3 5 88 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 88 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 88 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 88 253 (accept_3_3 2 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88
  253 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 88 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87
  253 (allA_succ_of_accept 86 87 253 (accept_3_3 86 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 87 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 85 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 84 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 253 (accept_3_3 83 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 253 (accept_3_3 80 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 253 (accept_3_3 77 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 253 (accept_3_3 74 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 253 (Polychromatic418967fa.accept_16_9_7_13_1_4997 73 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 253 (accept_3_3 71 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 253
  (Polychromatic418967fa.accept_12_9_3_1_1_303 69 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 253 (accept_3_3 68 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 253 (accept_3_3 65 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 253
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 63 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 253 (accept_3_3 62 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 253 (accept_3_3 59 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 253 (accept_3_3 56 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 253 (accept_3_3 53 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 253
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 253 (accept_3_3 50 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 253 (accept_3_3 47 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 253
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 253 (accept_3_3 44 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 253 (accept_3_3 41 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 253 (accept_3_3 38 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 253 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 253 (accept_3_3 35 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 253 (accept_3_3 32 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 253 (accept_3_3 29 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 253
  (Polychromatic418967fa.accept_13_1_9_6_1_146 27 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 253 (accept_3_3 26 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 253 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 253 (accept_3_3 23 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 253 (accept_3_3 20 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 253 (accept_3_3 17 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 253
  (Polychromatic418967fa.accept_10_5_7_3_1_561 15 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 253 (accept_3_3 14 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 253 (accept_3_3 11 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 253
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 253 (accept_3_3 8 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  253 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 253 (accept_3_3 5 87 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 87
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 253 (accept_3_3 2 87 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 253 (Polychromatic418967fa.accept_13_1_9_6_1_146 1
  87 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 253
  (allA_of_3_1 86 86 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 253 (allA_succ_of_accept 84 85 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 253 (accept_3_3 83 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 253 (Polychromatic418967fa.accept_10_2_5_3_1_1408 82 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 253 (Polychromatic418967fa.accept_16_1_5_13_1_1025 81 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 253 (accept_3_3 80 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 85 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 78 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 253 (accept_3_3 77 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 76 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 75 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 253 (accept_3_3 74 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 253 (Polychromatic418967fa.accept_16_9_5_13_1_4972 73 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 253
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 253 (accept_3_3 71 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 253 (accept_3_3 68 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 67 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 253 (accept_3_3 65 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 253 (Polychromatic418967fa.accept_13_12_7_6_1_1015 64 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 253 (Polychromatic418967fa.accept_15_3_10_13_1_2605 63 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 253 (accept_3_3 62 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 85 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 253 (accept_3_3 59 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 253 (Polychromatic418967fa.accept_10_8_5_3_1_543 58 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 253 (accept_3_3 56 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 253 (Polychromatic418967fa.accept_19_17_9_6_1_12658 55 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 253
  (Polychromatic418967fa.accept_19_16_9_6_1_5799 54 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 253 (accept_3_3 53 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 253 (accept_3_3 50 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 253 (Polychromatic418967fa.accept_15_4_10_13_1_2565 49 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 253 (accept_3_3 47 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 46 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 253 (Polychromatic418967fa.accept_22_1_19_11_1_12229 45 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 253 (accept_3_3 44 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 85 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 253 (accept_3_3 41 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 253 (Polychromatic418967fa.accept_13_1_7_6_1_142 40 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 253 (accept_3_3 38 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 253
  (Polychromatic418967fa.accept_19_17_9_6_1_12658 36 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 253 (accept_3_3 35 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 253 (accept_3_3 32 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 253 (accept_3_3 29 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 253 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 253 (accept_3_3 26 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 253 (accept_3_3 23 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 253 (Polychromatic418967fa.accept_10_2_5_3_1_1408 22 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 253 (accept_3_3 20 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 253 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 253
  (Polychromatic418967fa.accept_10_8_5_3_1_543 18 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 253 (accept_3_3 17 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 253 (accept_3_3 14 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 253 (Polychromatic418967fa.accept_19_13_9_6_1_4393 13 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 253 (accept_3_3 11 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 253 (Polychromatic418967fa.accept_16_10_5_13_1_8591 10 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 253 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 253 (accept_3_3 8 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 253 (accept_3_3 5 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  253 (Polychromatic418967fa.accept_13_4_7_6_1_2359 4 85 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 253 (accept_3_3 2 85 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 253 (Polychromatic418967fa.accept_13_1_7_6_1_142 1 85 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 253
  (allA_succ_of_accept 83 84 253 (accept_3_3 83 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  84 253 (Polychromatic418967fa.accept_15_7_9_13_1_3451 82 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 84 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 84 253 (accept_3_3 80 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 84 253 (accept_3_3 77 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  84 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 84 253 (Polychromatic418967fa.accept_18_3_12_1_1_3787 75 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 253 (accept_3_3 74 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 84 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 253
  (Polychromatic418967fa.accept_16_8_4_13_1_1014 72 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 253 (accept_3_3 71 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 253 (accept_3_3 68 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 253
  (Polychromatic418967fa.accept_24_18_12_13_1_15427 66 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 84 253 (accept_3_3 65 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 253 (Polychromatic418967fa.accept_15_4_9_13_1_2582 64 84 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 84 253 (Polychromatic418967fa.accept_15_3_9_13_1_1681 63 84
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 253 (accept_3_3 62 84 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 61
  84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 253 (accept_3_3 59 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 253 (accept_3_3 56 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 253 (Polychromatic418967fa.accept_16_7_4_13_1_1057 55 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 253
  (Polychromatic418967fa.accept_16_6_4_13_1_3841 54 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 253 (accept_3_3 53 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  84 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 253 (accept_3_3 50 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 253
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 48 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 253 (accept_3_3 47 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  84 253 (Polychromatic418967fa.accept_27_19_3_10_1_15426 46 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 253 (Polychromatic418967fa.accept_17_11_16_15_1_5467 45 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 253 (accept_3_3 44 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 84 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 253 (accept_3_3 41 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 253 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 253 (accept_3_3 38 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 253 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 253
  (Polychromatic418967fa.accept_19_17_8_6_1_7146 36 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 84 253 (accept_3_3 35 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  84 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 84 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 253 (accept_3_3 32 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 253
  (Polychromatic418967fa.accept_24_6_12_13_1_8587 30 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 253 (accept_3_3 29 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 253 (Polychromatic418967fa.accept_16_12_4_13_1_3827 28 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 253 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 253 (accept_3_3 26 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 253 (accept_3_3 23 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 253 (Polychromatic418967fa.accept_17_4_16_15_1_1212 21 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 253 (accept_3_3 20 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 253 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 84 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 253
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 253 (accept_3_3 17 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 253 (accept_3_3 14 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 253
  (Polychromatic418967fa.accept_16_12_4_13_1_3827 12 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 253 (accept_3_3 11 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 253 (Polychromatic418967fa.accept_22_10_18_11_1_15425 10 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 253 (accept_3_3 8 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 84 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 253 (accept_3_3 5 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  253 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 84 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 84 253 (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 84 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 253 (accept_3_3 2 84 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 84 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 253 (allA_of_3_1
  83 83 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 253 (allA_succ_of_accept 81 82 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 82 253 (accept_3_3 80 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  82 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 82 253 (Polychromatic418967fa.accept_20_18_2_13_1_5265 78 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 253 (accept_3_3 77 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 82 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 253 (accept_3_3 74 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 253 (Polychromatic418967fa.accept_13_7_4_6_1_3221 72 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 253 (accept_3_3 71 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 253 (Polychromatic418967fa.accept_13_5_4_6_1_2371 70 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 253 (accept_3_3 68 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 253 (accept_3_3 65 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 253 (accept_3_3 62 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 61 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 253 (accept_3_3 59 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 253 (Polychromatic418967fa.accept_20_18_2_13_1_5265 58 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 253 (accept_3_3 56 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 253 (Polychromatic418967fa.accept_13_2_4_6_1_2356 54 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 253 (accept_3_3 53 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 253 (accept_3_3 50 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 253 (Polychromatic418967fa.accept_13_10_4_6_1_3224 49 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 253 (accept_3_3 47 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 253 (accept_3_3 44 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 253 (Polychromatic418967fa.accept_22_20_16_11_1_7421 42 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 253 (accept_3_3 41 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 82 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 253 (accept_3_3 38 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 253 (Polychromatic418967fa.accept_13_11_4_6_1_1006 37 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 253 (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 253 (accept_3_3 35 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 82 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 253 (accept_3_3 32 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 253 (Polychromatic418967fa.accept_20_10_2_13_1_2560 30 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 253 (accept_3_3 29 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 82 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 253 (accept_3_3 26 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 253 (accept_3_3 23 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 253 (Polychromatic418967fa.accept_13_9_4_6_1_1005 22 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 253 (accept_3_3 20 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 253 (accept_3_3 17 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 253 (accept_3_3 14 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 253 (Polychromatic418967fa.accept_17_12_14_15_1_5561 12 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 253 (accept_3_3 11 82 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 82 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 253 (accept_3_3 8 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 82 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 253 (accept_3_3 5 82 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 82 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 253 (accept_3_3 2 82 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1
  82 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 253
  (allA_succ_of_accept 80 81 253 (accept_3_3 80 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 253 (Polychromatic418967fa.accept_13_1_3_6_1_158 79 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 253 (Polychromatic418967fa.accept_10_8_1_3_1_1374 78 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 253 (accept_3_3 77 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 75 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 253 (accept_3_3 74 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 253 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 253 (accept_3_3 71 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 253
  (Polychromatic418967fa.accept_16_5_1_13_1_1053 69 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 253 (accept_3_3 68 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 253 (Polychromatic418967fa.accept_15_7_6_13_1_936 67 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 253 (accept_3_3 65 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 253
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 253 (accept_3_3 62 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 253 (accept_3_3 59 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 253
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 57 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 253 (accept_3_3 56 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 253 (Polychromatic418967fa.accept_25_5_6_3_1_8333 55 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 253 (accept_3_3 53 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 253
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 253 (accept_3_3 50 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 253 (Polychromatic418967fa.accept_13_10_3_6_1_1003 49 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 253 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 253 (accept_3_3 47 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 253 (accept_3_3 44 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 253 (Polychromatic418967fa.accept_20_3_1_13_1_6742 43 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 253 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 253 (accept_3_3 41 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 253
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 253 (accept_3_3 38 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 253 (Polychromatic418967fa.accept_15_7_6_13_1_936 37 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 253 (accept_3_3 35 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 253 (accept_3_3 32 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 253 (Polychromatic418967fa.accept_16_14_1_13_1_2754 30 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 253 (accept_3_3 29 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 253
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 253 (accept_3_3 26 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 253 (Polychromatic418967fa.accept_16_9_1_13_1_1850 25 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 253 (accept_3_3 23 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 253
  (Polychromatic418967fa.accept_16_5_1_13_1_1053 21 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 253 (accept_3_3 20 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 253 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 253 (accept_3_3 17 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 253
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 253 (accept_3_3 14 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 253 (Polychromatic418967fa.accept_25_13_6_3_1_15424 13 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 253 (accept_3_3 11 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 253
  (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 253 (accept_3_3 8 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  253 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 253 (Polychromatic418967fa.accept_18_6_9_1_1_3769 6 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 253 (accept_3_3 5 81 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 253 (accept_3_3 2 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  253 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 81 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 253
  (allA_of_3_1 80 80 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 253 (allA_succ_of_accept 78 79 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 253 (accept_3_3 77 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 76 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 253 (accept_3_3 74 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 253
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 72 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 253 (accept_3_3 71 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 253 (accept_3_3 68 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 253 (accept_3_3 65 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 253 (Polychromatic418967fa.accept_10_4_9_3_1_1907 64 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 253 (Polychromatic418967fa.accept_22_19_13_11_1_12313 63 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 253 (accept_3_3 62 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 253 (Polychromatic418967fa.accept_13_9_1_6_1_510 61 79 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 253 (accept_3_3 59 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 253 (accept_3_3 56 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 253 (accept_3_3 53 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 253 (accept_3_3 50 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 253 (accept_3_3 47 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 253 (accept_3_3 44 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 253 (Polychromatic418967fa.accept_19_5_3_6_1_8642 43 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 253 (accept_3_3 41 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 253 (accept_3_3 38 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 253 (Polychromatic418967fa.accept_19_18_3_6_1_9989 37 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 253
  (Polychromatic418967fa.accept_10_6_9_3_1_935 36 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 253 (accept_3_3 35 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 253 (accept_3_3 32 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 253 (accept_3_3 29 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 253 (Polychromatic418967fa.accept_13_2_1_6_1_2365 28 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 253 (accept_3_3 26 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 253 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 253 (accept_3_3 23 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 253 (accept_3_3 20 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 253 (Polychromatic418967fa.accept_16_3_15_13_1_2825 19 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 253 (accept_3_3 17 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 253 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 253 (accept_3_3 14 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 253 (accept_3_3 11 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 253 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 253 (accept_3_3 8 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 253 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 79 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 253 (accept_3_3 5 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  253 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 79 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 79 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 253 (accept_3_3 2 79 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 253 (Polychromatic418967fa.accept_19_1_3_6_1_5827 1 79 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 253
  (allA_succ_of_accept 77 78 253 (accept_3_3 77 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  78 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 253 (accept_3_3 74 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 253 (Polychromatic418967fa.accept_17_5_10_15_1_5574 73 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 253
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 72 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 253 (accept_3_3 71 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 253 (Polychromatic418967fa.accept_15_9_3_13_1_1686 69 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 253 (accept_3_3 68 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 253 (accept_3_3 65 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 253 (Polychromatic418967fa.accept_24_16_6_13_1_13661 64 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 253 (accept_3_3 62 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 253
  (Polychromatic418967fa.accept_19_3_2_6_1_11398 60 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 253 (accept_3_3 59 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 253 (accept_3_3 56 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 253
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 54 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 253 (accept_3_3 53 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 253 (accept_3_3 50 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 253 (accept_3_3 47 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 46 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 253 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 253 (accept_3_3 44 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 253
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 42 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 253 (accept_3_3 41 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 253 (accept_3_3 38 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 253 (Polychromatic418967fa.accept_14_9_8_1_1_2381 37 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 253
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 253 (accept_3_3 35 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 253 (Polychromatic418967fa.accept_16_1_14_13_1_3834 33 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 253 (accept_3_3 32 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 253 (accept_3_3 29 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 253 (Polychromatic418967fa.accept_20_8_18_13_1_8326 28 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 253 (accept_3_3 26 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 253
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 253 (accept_3_3 23 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 253 (accept_3_3 20 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 253
  (Polychromatic418967fa.accept_21_18_15_1_1_9470 18 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 253 (accept_3_3 17 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 253 (accept_3_3 14 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 253 (accept_3_3 11 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 253 (Polychromatic418967fa.accept_15_10_3_13_1_4480 10 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 253 (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 253 (accept_3_3 8 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 253
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 253 (accept_3_3 5 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  253 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 78 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 253 (accept_3_3 2 78 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 253 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 78 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 253 (allA_of_3_1 77 77
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 253 (allA_succ_of_accept 75 76 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 253 (accept_3_3 74 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 253 (accept_3_3 71 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 76 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 253 (accept_3_3 68 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 253 (Polychromatic418967fa.accept_10_7_6_3_1_927 67 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 253 (accept_3_3 65 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 253 (Polychromatic418967fa.accept_17_13_8_15_1_8135 64 76 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 253 (accept_3_3 62 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 253 (accept_3_3 59 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 76 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 253 (accept_3_3 56 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 253 (Polychromatic418967fa.accept_15_10_1_13_1_2609 55 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 253 (accept_3_3 53 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 76 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 253 (accept_3_3 50 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 253 (accept_3_3 47 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 76 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 253 (accept_3_3 44 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 253 (accept_3_3 41 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 76 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 253 (accept_3_3 38 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 253 (Polychromatic418967fa.accept_16_4_12_13_1_990 36 76 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 253 (accept_3_3 35 76 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 76 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 253 (accept_3_3 32 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 253 (Polychromatic418967fa.accept_13_5_11_6_1_505 31 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 253 (accept_3_3 29 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 253 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 76 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 253 (accept_3_3 26 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 253 (accept_3_3 23 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 76 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 253 (accept_3_3 20 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 253 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 253 (accept_3_3 17 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 76 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 253 (accept_3_3 14 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 253 (Polychromatic418967fa.accept_17_13_8_15_1_8135 13 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 253 (accept_3_3 11 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 76 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 253 (accept_3_3 8 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 76 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 76 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 253 (accept_3_3 5 76 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 253 (Polychromatic418967fa.accept_13_4_11_6_1_1033 4 76 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 253 (accept_3_3 2 76 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 76
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 253 (allA_succ_of_accept
  74 75 253 (accept_3_3 74 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 73 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 253 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 253 (accept_3_3 71 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 69
  75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 253 (accept_3_3 68 75
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 67 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 75 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 253 (accept_3_3 65 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 75 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 253 (Polychromatic418967fa.accept_18_9_3_1_1_2559
  63 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 253 (accept_3_3 62
  75 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 253
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 75 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 253 (accept_3_3 59 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 75 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 253 (Polychromatic418967fa.accept_10_7_5_3_1_542
  57 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 253 (accept_3_3 56
  75 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 55 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 75 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 253 (accept_3_3 53 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 75 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 51
  75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 253 (accept_3_3 50 75
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 253
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 75 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 253 (accept_3_3 47 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 75 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 45
  75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 253 (accept_3_3 44 75
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 253
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 253 (accept_3_3 41 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 75 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 39
  75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 253 (accept_3_3 38 75
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 253
  (Polychromatic418967fa.accept_10_7_5_3_1_542 37 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 75 253 (Polychromatic418967fa.accept_17_2_7_15_1_5525 36 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 253 (accept_3_3 35 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 75 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 33
  75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 253 (accept_3_3 32 75
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 253 (Polychromatic418967fa.accept_7_3_5_1_1_72
  31 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 253 (accept_3_3 29 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 253 (accept_3_3 26 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 75 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 253 (accept_3_3 23 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 253 (accept_3_3 20 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 253 (Polychromatic418967fa.accept_17_2_7_15_1_5525 19 75 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 253 (accept_3_3 17 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 253 (accept_3_3 14 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 75 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 253
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 253 (accept_3_3 11 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 253 (accept_3_3 8 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 75 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 253 (accept_3_3 5 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 253 (accept_3_3 2 75 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 253 (Polychromatic418967fa.accept_19_1_18_6_1_3110 1 75 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 253 (allA_of_3_1 74 74
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 253 (allA_succ_of_accept 72 73 253
  (Polychromatic418967fa.accept_7_2_3_1_1_10 72 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 253 (accept_3_3 71 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 253 (Polychromatic418967fa.accept_16_6_9_13_1_2751 70 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 253 (Polychromatic418967fa.accept_16_5_9_13_1_3845 69 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 253 (accept_3_3 68 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 73 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 253
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 66 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 253 (accept_3_3 65 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 253 (Polychromatic418967fa.accept_17_13_5_15_1_8103 64 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 253 (Polychromatic418967fa.accept_13_11_8_6_1_1023 63 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 253 (accept_3_3 62 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 73 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 253 (accept_3_3 59 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 253 (Polychromatic418967fa.accept_21_15_10_1_1_15423 57 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 253 (accept_3_3 56 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 253 (Polychromatic418967fa.accept_16_7_9_13_1_4948 55 73
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 54 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 253 (accept_3_3 53 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 73 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 253 (accept_3_3 50 73 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 253 (Polychromatic418967fa.accept_16_1_9_13_1_1822 49 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 253
  (Polychromatic418967fa.accept_19_10_16_6_1_5773 48 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 253 (accept_3_3 47 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 253 (Polychromatic418967fa.accept_17_11_5_15_1_8144 45 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 253 (accept_3_3 44 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 253 (Polychromatic418967fa.accept_22_21_7_11_1_7486 43 73
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 253
  (Polychromatic418967fa.accept_27_15_19_10_1_15422 42 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 73 253 (accept_3_3 41 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 73 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 73 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 73 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 253 (accept_3_3 38 73 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 37
  73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 253
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 253 (accept_3_3 35 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 253 (Polychromatic418967fa.accept_19_15_16_6_1_9955 34 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 73 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 253 (accept_3_3 32 73 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 253 (Polychromatic418967fa.accept_19_12_16_6_1_7175 31 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 253
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 253 (accept_3_3 29 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 253 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 73 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 253 (accept_3_3 26 73 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 253
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 253 (accept_3_3 23 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 253 (Polychromatic418967fa.accept_16_6_9_13_1_2751 22 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 253 (Polychromatic418967fa.accept_16_5_9_13_1_3845 21 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 253 (accept_3_3 20 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 73 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 253 (accept_3_3 17 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 253 (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 73 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 253 (accept_3_3 14 73 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 253 (Polychromatic418967fa.accept_17_13_5_15_1_8103 13 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 253 (accept_3_3 11 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 253 (Polychromatic418967fa.accept_17_10_5_15_1_4332 10 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 73 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 253 (accept_3_3 8 73 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 253 (Polychromatic418967fa.accept_16_7_9_13_1_4948 7 73 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 253
  (Polychromatic418967fa.accept_16_6_9_13_1_2751 6 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 253 (accept_3_3 5 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  253 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 73 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 253 (Polychromatic418967fa.accept_19_3_16_6_1_1987 3 73 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 253 (accept_3_3 2 73 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 253 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 73 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 253 (allA_succ_of_accept 71
  72 253 (accept_3_3 71 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 253
  (Polychromatic418967fa.accept_15_10_12_13_1_2585 70 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 72 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 72 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 253 (accept_3_3 68 72 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 253 (Polychromatic418967fa.accept_16_3_8_13_1_3867 67 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 66 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 72 253 (accept_3_3 65 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  72 253 (Polychromatic418967fa.accept_13_12_7_6_1_1015 64 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 72 253 (Polychromatic418967fa.accept_15_3_12_13_1_2549 63 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 253 (accept_3_3 62 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 61 72 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 253
  (Polychromatic418967fa.accept_16_12_8_13_1_6073 60 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 72 253 (accept_3_3 59 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  72 253 (Polychromatic418967fa.accept_25_8_22_3_1_11821 58 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 72 253 (Polychromatic418967fa.accept_22_13_6_11_1_15421 57 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 253 (accept_3_3 56 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 72 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 253
  (Polychromatic418967fa.accept_19_16_15_6_1_12661 54 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 72 253 (accept_3_3 53 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 72 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 72 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 72 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 253 (accept_3_3 50 72 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 253
  (Polychromatic418967fa.accept_19_11_15_6_1_7173 49 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 72 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 72 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 253 (accept_3_3 47 72 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 72 253 (Polychromatic418967fa.accept_15_1_12_13_1_944 46 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 72 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 72 253 (accept_3_3 44 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  72 253 (Polychromatic418967fa.accept_13_4_7_6_1_2359 43 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 72 253 (Polychromatic418967fa.accept_19_4_15_6_1_9954 42 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 253 (accept_3_3 41 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 253 (Polychromatic418967fa.accept_13_1_7_6_1_142 40 72 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 72 253
  (Polychromatic418967fa.accept_20_19_12_13_1_2602 39 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 253 (accept_3_3 38 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 72 253 (Polychromatic418967fa.accept_16_5_8_13_1_2764 37 72 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 253 (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 72 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 253 (accept_3_3 35 72 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 34
  72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 72 253
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 33 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 72 253 (accept_3_3 32 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  72 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 72 253 (Polychromatic418967fa.accept_13_4_7_6_1_2359 30 72 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 253 (accept_3_3 29 72 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 253 (Polychromatic418967fa.accept_16_12_8_13_1_6073 28 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 72 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 72 253 (accept_3_3 26 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  72 253 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 72 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 72 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 253 (accept_3_3 23 72 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 253 (Polychromatic418967fa.accept_13_9_7_6_1_1673 22 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 72 253
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 72 253 (accept_3_3 20 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  72 253 (Polychromatic418967fa.accept_16_3_8_13_1_3867 19 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 72 253 (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 253 (accept_3_3 17 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 253 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 72
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 72 253
  (Polychromatic418967fa.accept_10_5_2_3_1_239 15 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 72 253 (accept_3_3 14 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  72 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 72 253 (Polychromatic418967fa.accept_13_12_7_6_1_1015 12 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 253 (accept_3_3 11 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 72 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 72 253
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 72 253 (accept_3_3 8 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72
  253 (Polychromatic418967fa.accept_22_7_6_11_1_13808 7 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 72 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 72 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 253 (accept_3_3 5 72 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 253 (Polychromatic418967fa.accept_13_4_7_6_1_2359 4 72 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 253 (accept_3_3 2 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72
  253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 72 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 253
  (allA_of_3_1 71 71 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 253 (allA_succ_of_accept 69 70 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 253 (accept_3_3 68 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 253 (accept_3_3 65 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 253 (accept_3_3 62 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 61 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 253 (accept_3_3 59 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 253 (accept_3_3 56 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 253 (Polychromatic418967fa.accept_21_12_7_1_1_9465 54 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 253 (accept_3_3 53 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 70 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 253 (accept_3_3 50 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 253 (accept_3_3 47 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 46 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 253 (accept_3_3 44 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 253 (accept_3_3 41 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 253 (accept_3_3 38 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 253 (Polychromatic418967fa.accept_13_11_5_6_1_519 37 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 253 (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 253 (accept_3_3 35 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 253 (Polychromatic418967fa.accept_15_4_10_13_1_2565 34 70
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 253 (accept_3_3 32 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 253 (accept_3_3 29 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 253 (accept_3_3 26 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 253 (Polychromatic418967fa.accept_13_12_5_6_1_1050 25 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 253 (accept_3_3 23 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 253 (accept_3_3 20 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 253 (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 253 (accept_3_3 17 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 70 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 253 (accept_3_3 14 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 253 (accept_3_3 11 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 253 (Polychromatic418967fa.accept_13_10_5_6_1_1671 10 70 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 253 (accept_3_3 8 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 70 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 253 (accept_3_3 5 70 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 70 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 70 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 253 (accept_3_3 2 70 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 253 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1
  70 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 253 (allA_succ_of_accept 68 69
  253 (accept_3_3 68 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 253
  (Polychromatic418967fa.accept_9_4_6_1_1_393 67 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 69 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 253 (accept_3_3 65 69 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 253 (Polychromatic418967fa.accept_12_3_9_1_1_290
  63 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 253 (accept_3_3 62
  69 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 69 253 (Polychromatic418967fa.accept_17_9_1_15_1_3156 60 69 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 253 (accept_3_3 59 69 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 69 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 57
  69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 253 (accept_3_3 56 69
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 253
  (Polychromatic418967fa.accept_19_17_12_6_1_8650 55 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 69 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 69 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 253 (accept_3_3 53 69 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 69 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 51
  69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 253 (accept_3_3 50 69
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 253
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 69 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 69 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 253 (accept_3_3 47 69 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 69 253 23 2 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 69 253 (Polychromatic418967fa.accept_21_3_6_1_1_4709 45 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 253 (accept_3_3 44 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 69 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 253
  (Polychromatic418967fa.accept_16_10_5_13_1_8591 42 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 253 (accept_3_3 41 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  69 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 253 (accept_3_3 38 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 69 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 253
  (Polychromatic418967fa.accept_10_6_9_3_1_935 36 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 253 (accept_3_3 35 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  69 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 253 (accept_3_3 32 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 69 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 253
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 69 253 (accept_3_3 29 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  69 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 69 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 253 (accept_3_3 26 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 69 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 253
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 23 69 253 23 1 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 22 69 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 69 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 253 (accept_3_3 20 69 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 19
  69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 253
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 253 (accept_3_3 17 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  69 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 253 (accept_3_3 14 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 69 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 253 (accept_3_3 11 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  69 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 253 (accept_3_3 8 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 69 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 253
  (Polychromatic418967fa.accept_10_6_9_3_1_935 6 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 253 (accept_3_3 5 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 69 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 253 (accept_3_3 2 69 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 253 (Polychromatic418967fa.accept_16_1_5_13_1_1025 1 69 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 253 (allA_of_3_1 68 68 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 253 (allA_succ_of_accept 66 67 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 253 (accept_3_3 65 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 253 (Polychromatic418967fa.accept_10_4_7_3_1_54 64 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 253 (Polychromatic418967fa.accept_16_15_3_13_1_2818 63 67 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 253 (accept_3_3 62 67 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 67 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 253 (accept_3_3 59 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 253 (accept_3_3 56 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 67 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 253 (accept_3_3 53 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 253 (accept_3_3 50 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 253 (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 67 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 253 (accept_3_3 47 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 253 (accept_3_3 44 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 67 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 253 (accept_3_3 41 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 253 (accept_3_3 38 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 253 (Polychromatic418967fa.accept_22_15_1_11_1_13763 37 67 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 253
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 253 (accept_3_3 35 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 253 (accept_3_3 32 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 67 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 253 (accept_3_3 29 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 253 (Polychromatic418967fa.accept_17_11_16_15_1_5467 28 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 253 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 253 (accept_3_3 26 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 67 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 253 (accept_3_3 23 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 253 (accept_3_3 20 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 67 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 253 (accept_3_3 17 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 253 (accept_3_3 14 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 253 (Polychromatic418967fa.accept_19_13_10_6_1_7147 13 67 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 253 (accept_3_3 11 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 253 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 253 (accept_3_3 8 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 253 (accept_3_3 5 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  253 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 67 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 67 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 253 (accept_3_3 2 67 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 253 (Polychromatic418967fa.accept_13_1_2_6_1_515 1 67 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 253 (allA_succ_of_accept 65 66
  253 (accept_3_3 65 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 253
  (Polychromatic418967fa.accept_15_4_6_13_1_956 64 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 253 (accept_3_3 62 66 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 66 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 60
  66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 253 (accept_3_3 59 66
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 253 (Polychromatic418967fa.accept_7_2_3_1_1_10
  58 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 66 253
  (Polychromatic418967fa.accept_10_7_6_3_1_927 57 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 66 253 (accept_3_3 56 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 66
  253 11 5 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  66 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 66 253 (accept_3_3 53 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 66 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 66 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 253 (accept_3_3 50 66 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 49
  66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 253
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 66 253 (accept_3_3 47 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  66 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 66 253 (Polychromatic418967fa.accept_29_16_8_21_1_15420 45 66 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 253 11 4 6 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 66 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 66 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 253 (accept_3_3 41 66 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 66 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 66 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 253 (accept_3_3 38 66
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 253 (Polychromatic418967fa.accept_7_2_3_1_1_10
  37 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 253
  (Polychromatic418967fa.accept_19_17_9_6_1_12658 36 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 253 (accept_3_3 35 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  66 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 66 253 11 3 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 66 253 (accept_3_3 32 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 66 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 66 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 253 (accept_3_3 29 66 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 253 (Polychromatic418967fa.accept_10_8_6_3_1_1394
  28 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 66 253 (accept_3_3 26 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  66 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 66 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 66 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 253 (accept_3_3 23 66 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 253 11 2 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 66 253 (Polychromatic418967fa.accept_13_8_1_6_1_997 21 66 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 253 (accept_3_3 20 66 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 253 (accept_3_3 17 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  66 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 253 (accept_3_3 14 66 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 66 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 66 253 11 1 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 66 253 (Polychromatic418967fa.accept_19_10_9_6_1_13992 10 66 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 66 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 253 (accept_3_3 8 66 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 253 (accept_3_3 5 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66
  253 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 66 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 66 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 253 (accept_3_3 2 66 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 66 253 (Polychromatic418967fa.accept_27_1_12_10_1_15419 1 66 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 253 (allA_of_3_1 65 65 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 253 (allA_succ_of_accept 63 64 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 253 (accept_3_3 62 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 253 (Polychromatic418967fa.accept_22_17_20_11_1_7481 61 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 253 (Polychromatic418967fa.accept_19_3_7_6_1_5791 60 64 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 253 (accept_3_3 59 64 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 253 (accept_3_3 56 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 253 (Polychromatic418967fa.accept_15_10_4_13_1_4506 55 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 253 (Polychromatic418967fa.accept_13_2_12_6_1_2394 54 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 253 (accept_3_3 53 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 253 (Polychromatic418967fa.accept_18_16_10_1_1_3696 52 64
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 253 (accept_3_3 50 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 253 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 253 (Polychromatic418967fa.accept_25_23_14_3_1_8295 48 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 253 (accept_3_3 47 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 64
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 253 (accept_3_3 44 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 253 (Polychromatic418967fa.accept_19_5_7_6_1_11379 43 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 253 (Polychromatic418967fa.accept_17_8_13_15_1_2143 42 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 253 (accept_3_3 41 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 253 (Polychromatic418967fa.accept_15_10_4_13_1_4506 40 64
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 253 (accept_3_3 38 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 253 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 253 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 253 (accept_3_3 35 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 64
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 253 (accept_3_3 32 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 253 (Polychromatic418967fa.accept_13_5_12_6_1_508 31 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 253 (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 64 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 253 (accept_3_3 29 64 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 253 (Polychromatic418967fa.accept_13_2_12_6_1_2394 28 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 253 (accept_3_3 26 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 253 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 253 (Polychromatic418967fa.accept_15_9_4_13_1_4482 24 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 253 (accept_3_3 23 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 64
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 253 (accept_3_3 20 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 253 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 253 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 64 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 253 (accept_3_3 17 64 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 253 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 253 (accept_3_3 14 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 253 (Polychromatic418967fa.accept_18_13_10_1_1_9025 13 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 253 (Polychromatic418967fa.accept_24_12_16_13_1_11972 12 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 253 (accept_3_3 11 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 64
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 253 (accept_3_3 8 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  253 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 253 (Polychromatic418967fa.accept_15_6_4_13_1_403 6 64 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 253 (accept_3_3 5 64 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 253 (Polychromatic418967fa.accept_26_4_12_19_1_15418 4 64 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 253 (accept_3_3 2 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64
  253 (Polychromatic418967fa.accept_19_1_7_6_1_1959 1 64 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 64 253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 253
  (allA_succ_of_accept 62 63 253 (accept_3_3 62 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 253 (Polychromatic418967fa.accept_15_1_3_13_1_2548 61 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 253 (Polychromatic418967fa.accept_13_8_11_6_1_1035 60 63 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 253 (accept_3_3 59 63 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 253
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 253 (accept_3_3 56 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 253 (Polychromatic418967fa.accept_14_13_7_1_1_1618 55 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 253 (accept_3_3 53 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 253
  (Polychromatic418967fa.accept_16_3_15_13_1_2825 51 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 253 (accept_3_3 50 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 253 (Polychromatic418967fa.accept_25_24_13_3_1_15417 49 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 253 (Polychromatic418967fa.accept_14_6_7_1_1_78 48 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 253 (accept_3_3 47 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 253
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 253 (accept_3_3 44 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 253 (Polychromatic418967fa.accept_13_4_11_6_1_1033 43 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 253 (accept_3_3 41 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 253
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 253 (accept_3_3 38 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 253 (Polychromatic418967fa.accept_17_3_12_15_1_1203 37 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 253 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 253 (accept_3_3 35 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 253
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 253 (accept_3_3 32 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 253 (Polychromatic418967fa.accept_13_5_11_6_1_505 31 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 253 (accept_3_3 29 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 253
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 253 (accept_3_3 26 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 253 (Polychromatic418967fa.accept_15_10_3_13_1_4480 25 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 253 (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 63 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 253 (accept_3_3 23 63 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 253
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 253 (accept_3_3 20 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 253 (Polychromatic418967fa.accept_16_3_15_13_1_2825 19 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 253 (accept_3_3 17 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 253
  (Polychromatic418967fa.accept_25_15_13_3_1_15416 15 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 63 253 (accept_3_3 14 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 253 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 63 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 253 (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 63
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 253 (accept_3_3 11 63 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 253
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 253 (accept_3_3 8 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  253 (Polychromatic418967fa.accept_24_7_15_13_1_8570 7 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 253 (accept_3_3 5 63 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 253
  (Polychromatic418967fa.accept_16_3_15_13_1_2825 3 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 253 (accept_3_3 2 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  253 (Polychromatic418967fa.accept_15_1_3_13_1_2548 1 63 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 253
  (allA_of_3_1 62 62 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 253 (allA_succ_of_accept 60 61 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 253 (accept_3_3 59 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 253 (accept_3_3 56 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 61 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 253
  (Polychromatic418967fa.accept_13_2_9_6_1_501 54 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 253 (accept_3_3 53 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 253 (accept_3_3 50 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 61 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 253 (accept_3_3 47 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 253 (accept_3_3 44 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 253 (Polychromatic418967fa.accept_13_4_9_6_1_2376 43 61 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 253 (accept_3_3 41 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 253 (accept_3_3 38 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 253 (Polychromatic418967fa.accept_21_16_19_1_1_6320 37 61 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 253
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 253 (accept_3_3 35 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 253 (accept_3_3 32 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 61 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 253 (accept_3_3 29 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 253 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 253 (accept_3_3 26 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 61 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 253 (accept_3_3 23 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 253 (accept_3_3 20 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 253 (Polychromatic418967fa.accept_17_2_10_15_1_1238 19 61 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 253 (accept_3_3 17 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 253 (Polychromatic418967fa.accept_13_3_9_6_1_502 16 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 253 (accept_3_3 14 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 61 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 253 (accept_3_3 11 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 253 (Polychromatic418967fa.accept_22_9_17_11_1_5877 9 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 253 (accept_3_3 8 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 253 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 61 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 253 (accept_3_3 5 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  253 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 61 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 61 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 253 (accept_3_3 2 61 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 253 (Polychromatic418967fa.accept_13_1_9_6_1_146 1 61 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 253 (allA_succ_of_accept 59 60 253 (accept_3_3 59 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 60 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 60 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 253 (accept_3_3 56 60 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 253 (Polychromatic418967fa.accept_19_17_3_6_1_8662
  55 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 253 (accept_3_3 53 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 253 (Polychromatic418967fa.accept_21_9_18_1_1_9424 51 60 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 253 (accept_3_3 50 60 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 60 253 (accept_3_3 47 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  60 253 (Polychromatic418967fa.accept_19_8_3_6_1_9982 46 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 60 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 253 (accept_3_3 44 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 60 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 253
  (Polychromatic418967fa.accept_16_10_12_13_1_4950 42 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 60 253 (accept_3_3 41 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 60 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 60 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 60 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 253 (accept_3_3 38 60 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 253 (Polychromatic418967fa.accept_13_11_8_6_1_1023
  37 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 253
  (Polychromatic418967fa.accept_16_4_12_13_1_990 36 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 253 (accept_3_3 35 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 253 (accept_3_3 32 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 60 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 253 (accept_3_3 29 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 253 (Polychromatic418967fa.accept_13_2_8_6_1_2390 28 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 253 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 253 (accept_3_3 26 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 60 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 253 (accept_3_3 23 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 253 (accept_3_3 20 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 60 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 253
  (Polychromatic418967fa.accept_17_1_9_15_1_3186 18 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 253 (accept_3_3 17 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 253 (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 253 (accept_3_3 14 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 60 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 253 (accept_3_3 11 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 253 (accept_3_3 8 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 253
  (Polychromatic418967fa.accept_17_6_9_15_1_3185 6 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 253 (accept_3_3 5 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  253 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 60 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 253 (accept_3_3 2 60 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 60 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 253))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 253 (allA_of_3_1 59 59 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 253
  (allA_succ_of_accept 57 58 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 58 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 253 (accept_3_3 56 58 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 253
  (Polychromatic418967fa.accept_22_10_14_11_1_12225 54 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 58 253 (accept_3_3 53 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 58 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 58 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 253 (accept_3_3 50 58 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 58 253 (Polychromatic418967fa.accept_19_11_1_6_1_5752
  49 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 58 253 (accept_3_3 47 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  58 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 46 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 253 (accept_3_3 44 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 253 (accept_3_3 41 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 253 (accept_3_3 38 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 253 (Polychromatic418967fa.accept_16_5_10_13_1_6042 37 58 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 253
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 253 (accept_3_3 35 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 253 (accept_3_3 32 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 253 (accept_3_3 29 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 253 (accept_3_3 26 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 58 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 253 (accept_3_3 23 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 253 (Polychromatic418967fa.accept_14_8_2_1_1_1652 22 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 253 (accept_3_3 20 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 253
  (Polychromatic418967fa.accept_19_18_1_6_1_5807 18 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 253 (accept_3_3 17 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 253 (accept_3_3 14 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 58 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 253 (accept_3_3 11 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 253 (accept_3_3 8 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 253 (accept_3_3 5 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  253 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 58 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 58 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 253 (accept_3_3 2 58 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 253 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 58 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 253 (allA_succ_of_accept 56 57 253
  (accept_3_3 56 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 253
  (Polychromatic418967fa.accept_10_5_7_3_1_561 55 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 253 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 253 (accept_3_3 53 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 51
  57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 253 (accept_3_3 50 57
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 253
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 253 (Polychromatic418967fa.accept_15_3_12_13_1_2549 48 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 253 (accept_3_3 47 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 57 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 253 (Polychromatic418967fa.accept_10_5_7_3_1_561
  45 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 253 (accept_3_3 44
  57 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 253
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 253 (accept_3_3 41 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 253 (Polychromatic418967fa.accept_12_3_9_1_1_290
  39 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 253 (accept_3_3 38
  57 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 253
  (Polychromatic418967fa.accept_13_11_5_6_1_519 37 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 253 (accept_3_3 35 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 57 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 33
  57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 253 (accept_3_3 32 57
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 253
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 253 (Polychromatic418967fa.accept_13_4_5_6_1_3201 30 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 253 (accept_3_3 29 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 253 (Polychromatic418967fa.accept_12_3_9_1_1_290
  27 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 253 (accept_3_3 26
  57 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 253
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 253 (accept_3_3 23 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 57 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 253 (Polychromatic418967fa.accept_16_5_9_13_1_3845
  21 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 253 (accept_3_3 20
  57 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 253
  (Polychromatic418967fa.accept_21_19_15_1_1_6345 19 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 253 (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 253 (accept_3_3 17 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 15
  57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 253 (accept_3_3 14 57
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 253
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 253 (accept_3_3 11 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 253 (Polychromatic418967fa.accept_17_9_6_15_1_5454
  9 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 253 (accept_3_3 8 57
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 253 (Polychromatic418967fa.accept_9_7_3_1_1_386
  7 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 253 (accept_3_3 5 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 253 (accept_3_3 2 57 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 253 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 57 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 253 (allA_of_3_1 56 56 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 253
  (allA_succ_of_accept 54 55 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 253 (accept_3_3 53 55 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 253 (Polychromatic418967fa.accept_10_2_5_3_1_1408 52 55 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 51
  55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 253 (accept_3_3 50 55
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 253
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 49 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 253 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 55 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 253 (accept_3_3 47 55 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 253
  (Polychromatic418967fa.accept_17_11_4_15_1_3150 45 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 55 253 11 4 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 55 253 (Polychromatic418967fa.accept_24_19_7_13_1_10414 43 55 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 253 (accept_3_3 41 55 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 40
  55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 253
  (Polychromatic418967fa.accept_24_15_7_13_1_13690 39 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 253 (accept_3_3 38 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 55 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 253 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 55
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 253 (accept_3_3 35 55 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34
  55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 55 253 11 3 5 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 55 253 (accept_3_3 32
  55 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 253
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 31 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 55 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 253 (accept_3_3 29 55 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 55 253 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 55 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 253 (Polychromatic418967fa.accept_10_7_5_3_1_542
  27 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 253 (accept_3_3 26
  55 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 253
  (Polychromatic418967fa.accept_16_9_7_13_1_4997 25 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 55 253 (Polychromatic418967fa.accept_29_24_26_21_1_15415 24 55 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 253 (accept_3_3 23 55 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 55 253 11 2 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 55 253 (Polychromatic418967fa.accept_14_7_13_1_1_922 21 55 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 253 (accept_3_3 20 55 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 55 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 253 (accept_3_3 17 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 253 (Polychromatic418967fa.accept_24_15_7_13_1_13690 15 55 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 253 (accept_3_3 14 55 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 253 (Polychromatic418967fa.accept_19_13_17_6_1_11363 13 55
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 55 253 11 1 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 55 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 55 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 253 (accept_3_3 8 55 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 7
  55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 253 (accept_3_3 5 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  253 (Polychromatic418967fa.accept_15_4_10_13_1_2565 4 55 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 55 253 (Polychromatic418967fa.accept_15_3_10_13_1_2605 3 55 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 253 (accept_3_3 2 55 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 253 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 55 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  253))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 253 (allA_succ_of_accept 53 54 253
  (accept_3_3 53 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 52 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 54 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 253 (accept_3_3 50 54 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 54 253 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 54 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 48
  54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 253 (accept_3_3 47 54
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 46 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 54 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 54 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 253 (accept_3_3 44 54 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 54 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 253
  (Polychromatic418967fa.accept_24_18_6_13_1_15414 42 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 54 253 (accept_3_3 41 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 253 (Polychromatic418967fa.accept_13_1_2_6_1_515 40 54 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 54 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 253 (accept_3_3 38 54 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 253 (Polychromatic418967fa.accept_10_7_4_3_1_560
  37 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 253
  (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 253 (accept_3_3 35 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 253 (Polychromatic418967fa.accept_15_3_9_13_1_1681 33 54 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 253 (accept_3_3 32 54 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 253
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 30 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 253 (accept_3_3 29 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 253 (Polychromatic418967fa.accept_19_9_16_6_1_5774 28 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 253 (accept_3_3 26 54 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 54 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 253
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 253 (accept_3_3 23 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 253 (Polychromatic418967fa.accept_13_9_2_6_1_514 22 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 253 (Polychromatic418967fa.accept_13_8_2_6_1_2385 21 54 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 253 (accept_3_3 20 54 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 253 (accept_3_3 17 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 253 (Polychromatic418967fa.accept_24_16_6_13_1_13661 16 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 253 (accept_3_3 14 54 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 54 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 253
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 253 (accept_3_3 11 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 253 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 54 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 253 (accept_3_3 8 54 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 253 (accept_3_3 5 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  253 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 54 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 54 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 253 (accept_3_3 2 54 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 54 253 (Polychromatic418967fa.accept_13_1_2_6_1_515 1 54 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 253))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 253 (allA_of_3_1 53 53 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 253
  (allA_succ_of_accept 51 52 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 253 (accept_3_3 50 52 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 48
  52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 253 (accept_3_3 47 52
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 253 (Polychromatic418967fa.accept_7_4_3_1_1_87
  46 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 52 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 52 253 (accept_3_3 44 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  52 253 (Polychromatic418967fa.accept_17_9_1_15_1_3156 43 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 52 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 253 (accept_3_3 41 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 52 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 52 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 52 253 (accept_3_3 38 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  52 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 52 253 (Polychromatic418967fa.accept_15_6_7_13_1_1666 36 52 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 253 (accept_3_3 35 52 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 52
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 253 (accept_3_3 32 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 253 (accept_3_3 29 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 253 (Polychromatic418967fa.accept_16_12_4_13_1_3827 28 52 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 52 253 (accept_3_3 26 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  52 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 52 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 253 (accept_3_3 23 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 52 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 253 (accept_3_3 20 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 253 (accept_3_3 17 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 52 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 253 (accept_3_3 14 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  52 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 52 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 253 (accept_3_3 11 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 52 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 253 (accept_3_3 8 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52
  253 (Polychromatic418967fa.accept_16_7_4_13_1_1057 7 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 52 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 253 (accept_3_3 5 52 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 52 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 52 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 52 253 (accept_3_3 2 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52
  253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 52 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 253)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 253 (allA_succ_of_accept 50 51 253
  (accept_3_3 50 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 253
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 253 (accept_3_3 47 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 45
  51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 253 (accept_3_3 44 51
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 253
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 253 (accept_3_3 41 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 39
  51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 253 (accept_3_3 38 51
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 253
  (Polychromatic418967fa.accept_15_7_6_13_1_936 37 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 51 253 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 253 (accept_3_3 35 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 51 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 253 (Polychromatic418967fa.accept_12_9_3_1_1_303
  33 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 253 (accept_3_3 32
  51 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 51 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 253 (accept_3_3 29 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 51 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 27
  51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 253 (accept_3_3 26 51
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 253
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 51 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 253 (accept_3_3 23 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 51 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21
  51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 253 (accept_3_3 20 51
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 253
  (Polychromatic418967fa.accept_15_4_6_13_1_956 19 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 51 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 253 (accept_3_3 17 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 51 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 253 (Polychromatic418967fa.accept_13_2_12_6_1_2394
  15 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 253 (accept_3_3 14
  51 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 51 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 253 (accept_3_3 11 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 51 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 253 (accept_3_3 8 51 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 7
  51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 253 (accept_3_3 5 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 253 (accept_3_3 2 51 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 253 (Polychromatic418967fa.accept_16_1_3_13_1_2785 1 51 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 253)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 253 (allA_of_3_1 50 50 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 253
  (allA_succ_of_accept 48 49 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 253 (accept_3_3 47 49 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 253 (Polychromatic418967fa.accept_10_6_9_3_1_935 46 49 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 253 (Polychromatic418967fa.accept_21_3_7_1_1_9521
  45 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 253 (accept_3_3 44
  49 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 253
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 49 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 253 (accept_3_3 41 49 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 253 (Polychromatic418967fa.accept_15_10_4_13_1_4506 40 49 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 253 (accept_3_3 38 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 253 (Polychromatic418967fa.accept_16_5_1_13_1_1053 37 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 253 (accept_3_3 35 49 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 49 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 253 (accept_3_3 32 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 253 (Polychromatic418967fa.accept_13_5_10_6_1_2361 31 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 49 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 253 (accept_3_3 29 49 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 49 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 253
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 253 (accept_3_3 26 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 253 (accept_3_3 23 49 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 253 (Polychromatic418967fa.accept_13_9_10_6_1_1028 22 49 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 253
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 253 (accept_3_3 20 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 253 (Polychromatic418967fa.accept_16_3_1_13_1_4968 19 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 253 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 49 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 253 (accept_3_3 17 49 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 253 (accept_3_3 14 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 253 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 253 (accept_3_3 11 49 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 253 (Polychromatic418967fa.accept_15_10_4_13_1_4506 10 49 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 253
  (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 253 (accept_3_3 8 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 49 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 253 (accept_3_3 5 49 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 253 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 49 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 49
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 253 (accept_3_3 2 49 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 253 (Polychromatic418967fa.accept_19_1_11_6_1_7152
  1 49 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  253))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 253 (allA_succ_of_accept 47 48 253 (accept_3_3 47
  48 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 253
  (Polychromatic418967fa.accept_10_6_8_3_1_930 46 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 253 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 48 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 253 (accept_3_3 44 48 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 48 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 42
  48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 253 (accept_3_3 41 48
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 40 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 48 253 (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 48 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 253 (accept_3_3 38 48 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 48 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 48 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 253 (Polychromatic418967fa.accept_10_6_8_3_1_930
  36 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 253 (accept_3_3 35
  48 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 253
  (Polychromatic418967fa.accept_9_7_3_1_1_386 34 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 48 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 48 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 253 (accept_3_3 32 48 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 48 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 48 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 30
  48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 253 (accept_3_3 29 48
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 253
  (Polychromatic418967fa.accept_13_2_9_6_1_501 28 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 48 253 (Polychromatic418967fa.accept_13_1_9_6_1_146 27 48 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 253 (accept_3_3 26 48 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 48 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 48 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 24
  48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 253 (accept_3_3 23 48
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 253
  (Polychromatic418967fa.accept_9_4_3_1_1_154 22 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 48 253 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 48 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 253 (accept_3_3 20 48 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 48 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 48 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 253
  (Polychromatic418967fa.accept_20_18_8_13_1_6761 18 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 253 (accept_3_3 17 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 48 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 253 (accept_3_3 14 48 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 253 (accept_3_3 11 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 253 (Polychromatic418967fa.accept_13_10_9_6_1_1026 10 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 253 (accept_3_3 8 48 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 253 (accept_3_3 5 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  253 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 48 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 253 (Polychromatic418967fa.accept_13_3_9_6_1_502 3 48 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 253 (accept_3_3 2 48 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 253 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 48 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 253)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 253 (allA_of_3_1 47 47 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 253 (allA_succ_of_accept 45 46
  253 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 253 (accept_3_3 44 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 253 (Polychromatic418967fa.accept_15_12_1_13_1_3444 42 46 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 253 (accept_3_3 41 46 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 46 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 253 (accept_3_3 38 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 253 (Polychromatic418967fa.accept_10_7_6_3_1_927 37 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 253 (Polychromatic418967fa.accept_19_17_8_6_1_7146 36 46 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 253 (accept_3_3 35 46 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 253 (Polychromatic418967fa.accept_18_16_10_1_1_3696 34 46
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 253 (accept_3_3 32 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 253 (Polychromatic418967fa.accept_13_4_7_6_1_2359 30 46 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 253 (accept_3_3 29 46 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 253 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 46 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 253 (accept_3_3 26 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 253 (Polychromatic418967fa.accept_13_12_7_6_1_1015 25 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 46 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 23 46 253 23 1 2 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 22 46 253 (Polychromatic418967fa.accept_13_9_7_6_1_1673
  22 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 253 (accept_3_3 20 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 253 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 46 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 253 (accept_3_3 17 46 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 46 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 253 (accept_3_3 14 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 253 (Polychromatic418967fa.accept_18_13_10_1_1_9025 13 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 46 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 253 (accept_3_3 11 46 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 46 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 253 (accept_3_3 8 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 253 (Polychromatic418967fa.accept_22_6_2_11_1_13769 6 46 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 253 (accept_3_3 5 46 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 46 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 253 (accept_3_3 2 46 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 253 (Polychromatic418967fa.accept_13_1_7_6_1_142 1
  46 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  253)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 253 (allA_succ_of_accept 44 45 253 (accept_3_3 44 45
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 253
  (Polychromatic418967fa.accept_19_5_7_6_1_11379 43 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 253 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 45 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 253 (accept_3_3 41 45 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 39
  45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 253 (accept_3_3 38 45
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 253 (Polychromatic418967fa.accept_7_2_3_1_1_10
  37 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 253
  (Polychromatic418967fa.accept_21_15_3_1_1_6338 36 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 253 (accept_3_3 35 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 253 (accept_3_3 32 45 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 253 (Polychromatic418967fa.accept_21_10_3_1_1_3323 31 45 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 253
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 253 (accept_3_3 29 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 45 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 253 (accept_3_3 26 45 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 45 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 253
  (Polychromatic418967fa.accept_18_6_9_1_1_3769 24 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 253 (accept_3_3 23 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 253 (Polychromatic418967fa.accept_17_4_11_15_1_3170 21 45 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 253 (accept_3_3 20 45 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 45 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 253 (accept_3_3 17 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 45 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 253 (accept_3_3 14 45 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 253 (Polychromatic418967fa.accept_17_13_11_15_1_5556 13 45 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 253 (accept_3_3 11 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 253 (accept_3_3 8 45 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 45 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 253
  (Polychromatic418967fa.accept_18_6_9_1_1_3769 6 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 253 (accept_3_3 5 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 45 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 253 (accept_3_3 2 45 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 253 (Polychromatic418967fa.accept_19_1_7_6_1_1959 1 45 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 253))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  253 (allA_of_3_1 44 44 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 253 (allA_succ_of_accept 42 43 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 253 (accept_3_3 41 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 43 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 253 (accept_3_3 38 43 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 253 (Polychromatic418967fa.accept_13_11_4_6_1_1006 37 43 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 253
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 253 (accept_3_3 35 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 43 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 253 (accept_3_3 32 43 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 43 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 253 (accept_3_3 29 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 253 (Polychromatic418967fa.accept_13_2_4_6_1_2356 28 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 253 (Polychromatic418967fa.accept_25_2_18_3_1_15413 27 43 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 253 (accept_3_3 26 43 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 253 (Polychromatic418967fa.accept_22_3_21_11_1_12298 25 43
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 253 (accept_3_3 23 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 43 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 253 (accept_3_3 20 43 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 253 (Polychromatic418967fa.accept_22_19_21_11_1_10765 19 43 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 253 (accept_3_3 17 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 253 (Polychromatic418967fa.accept_18_16_7_1_1_6332 16 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 43 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 253 (accept_3_3 14 43 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 43 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 253
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 253 (accept_3_3 11 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 253 (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 43 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 253 (accept_3_3 8 43 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 253 (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 43 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 253 (accept_3_3 5 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  253 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 43 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 43 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 253 (accept_3_3 2 43 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 253 (Polychromatic418967fa.accept_17_1_9_15_1_3186 1 43 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 253))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 253
  (allA_succ_of_accept 41 42 253 (accept_3_3 41 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 253 (accept_3_3 38 42 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 253 (Polychromatic418967fa.accept_16_5_10_13_1_6042 37 42 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 253
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 253 (accept_3_3 35 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 253 (Polychromatic418967fa.accept_15_3_12_13_1_2549 33 42 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 253 (accept_3_3 32 42 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 253 (accept_3_3 29 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 253 (Polychromatic418967fa.accept_16_12_10_13_1_1042 28 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 253 (accept_3_3 26 42 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 42 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 253
  (Polychromatic418967fa.accept_19_5_4_6_1_11375 24 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 253 (accept_3_3 23 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 42 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 253 (accept_3_3 20 42 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 253
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 253 (accept_3_3 17 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 253 (accept_3_3 14 42 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 42 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 253
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 253 (accept_3_3 11 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 253 (Polychromatic418967fa.accept_13_10_3_6_1_1003 10 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 253 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 42 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 253 (accept_3_3 8 42 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 253
  (Polychromatic418967fa.accept_17_6_8_15_1_10655 6 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 253 (accept_3_3 5 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  253 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 42 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 253 (accept_3_3 2 42 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 42 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 253)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 253
  (allA_of_3_1 41 41 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 253 (allA_succ_of_accept 39 40 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 253 (accept_3_3 38 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 253 (Polychromatic418967fa.accept_16_5_8_13_1_2764 37 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 253 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 40 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 253 (accept_3_3 35 40 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 40 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 253 (accept_3_3 32 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 40 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 253 (accept_3_3 29 40 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 253 (Polychromatic418967fa.accept_13_2_1_6_1_2365 28 40 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 253 (accept_3_3 26 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 40 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 253 (accept_3_3 23 40 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 40 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 253 (accept_3_3 20 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 253 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 40 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 253 (accept_3_3 17 40 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 40 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 253 (accept_3_3 14 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 40 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 253 (accept_3_3 11 40 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 40 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 253 (accept_3_3 8 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 40 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 253 (accept_3_3 5 40 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 40 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 253 (accept_3_3 2 40 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 253 (Polychromatic418967fa.accept_15_1_10_13_1_939
  1 40 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  253)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 253 (allA_succ_of_accept 38 39 253 (accept_3_3 38 39 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 253 (Polychromatic418967fa.accept_15_7_9_13_1_3451
  37 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 253
  (Polychromatic418967fa.accept_10_6_9_3_1_935 36 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 253 (accept_3_3 35 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 39 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 253 (accept_3_3 32 39 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 39 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 253 (accept_3_3 29 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 253 (Polychromatic418967fa.accept_17_10_5_15_1_4332 27 39 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 253 (accept_3_3 26 39 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 39 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 253 (accept_3_3 23 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 39 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 253 (accept_3_3 20 39 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 39 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 253 (accept_3_3 17 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 39 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 253 (accept_3_3 14 39 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 39 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 253 (accept_3_3 11 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 39 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 253 (accept_3_3 8 39 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 39 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 253 (accept_3_3 5 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 253 (accept_3_3 2 39 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 253 (Polychromatic418967fa.accept_25_1_14_3_1_15412 1 39 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 253))))))))))))))))))))))))))))))))))))))) (allB_succ 38 253
  (allA_of_3_1 38 38 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 253 (allA_succ_of_accept 36 37 253
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 253 (accept_3_3 35 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 253 (Polychromatic418967fa.accept_16_1_5_13_1_1025 33 37 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 253 (accept_3_3 32 37 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 37 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 253
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 30 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 253 (accept_3_3 29 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 253 (Polychromatic418967fa.accept_19_9_18_6_1_5778 28 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 37 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 253 (accept_3_3 26 37 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 37 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 253 (accept_3_3 23 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 253 (Polychromatic418967fa.accept_14_8_9_1_1_3313 22 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 253 (Polychromatic418967fa.accept_13_8_11_6_1_1035 21 37 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 253 (accept_3_3 20 37 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 253 (Polychromatic418967fa.accept_21_19_16_1_1_2053 19 37
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 253
  (Polychromatic418967fa.accept_13_5_11_6_1_505 18 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 253 (accept_3_3 17 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 253 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 37 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 253 (accept_3_3 14 37 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 37 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 253
  (Polychromatic418967fa.accept_17_12_3_15_1_5476 12 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 253 (accept_3_3 11 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 253 (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 37 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 253 (accept_3_3 8 37 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 253 (Polychromatic418967fa.accept_19_7_18_6_1_3095 7 37 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 253 (accept_3_3 5 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  253 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 37 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 37 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 253 (accept_3_3 2 37 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 253 (Polychromatic418967fa.accept_16_1_5_13_1_1025 1 37 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 253))))))))))))))))))))))))))))))))))))) (allB_succ 36 253
  (allA_succ_of_accept 35 36 253 (accept_3_3 35 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  36 253 (Polychromatic418967fa.accept_15_4_6_13_1_956 34 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 36 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 36 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 253 (accept_3_3 32 36 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 253 (Polychromatic418967fa.accept_13_5_10_6_1_2361 31 36 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 253
  (Polychromatic418967fa.accept_13_4_10_6_1_989 30 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 253 (accept_3_3 29 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 253 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 253 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 36 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 253 (accept_3_3 26 36 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 36 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 253
  (Polychromatic418967fa.accept_16_8_4_13_1_1014 24 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 253 (accept_3_3 23 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 253 (Polychromatic418967fa.accept_13_9_10_6_1_1028 22 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 253 (Polychromatic418967fa.accept_14_7_8_1_1_1621 21 36 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 253 (accept_3_3 20 36 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 253 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 36 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 253
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 253 (accept_3_3 17 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 253 (Polychromatic418967fa.accept_13_3_10_6_1_2382 16 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 253 (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 36 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 253 (accept_3_3 14 36 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 253 (Polychromatic418967fa.accept_17_13_2_15_1_2151 13 36
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 253
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 253 (accept_3_3 11 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 253 (Polychromatic418967fa.accept_17_10_2_15_1_3179 10 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 36 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 253 (accept_3_3 8 36 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 253 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 36 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 253
  (Polychromatic418967fa.accept_16_6_4_13_1_3841 6 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 253 (accept_3_3 5 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  253 (Polychromatic418967fa.accept_13_4_10_6_1_989 4 36 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 253 (Polychromatic418967fa.accept_13_3_10_6_1_2382 3 36 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 253 (accept_3_3 2 36 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 253)))))))))))))))))))))))))))))))))))) (allB_succ 35
  253 (allA_of_3_1 35 35 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 253 (allA_succ_of_accept 33 34 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 253 (accept_3_3 32 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 34 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 253 (accept_3_3 29 34 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 34 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 253 (accept_3_3 26 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 253 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 34 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 253 (accept_3_3 23 34 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 34 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 253 (accept_3_3 20 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 253 (Polychromatic418967fa.accept_22_18_12_11_1_5892 18 34 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 253 (accept_3_3 17 34 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 34 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 253 (accept_3_3 14 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 34 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 253 (accept_3_3 11 34 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 253 (Polychromatic418967fa.accept_15_10_4_13_1_4506 10 34 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 253 (accept_3_3 8 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 34 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 253 (accept_3_3 5 34 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 34 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 253 (accept_3_3 2 34 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 253 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1
  34 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 253))))))))))))))))))))))))))))))))))
  (allB_succ 33 253 (allA_succ_of_accept 32 33 253 (accept_3_3 32 33 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 33 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 33 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 253 (accept_3_3 29 33 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  33 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 33 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 253 (accept_3_3 26 33 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 253 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 33 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 253 (accept_3_3 23 33 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 33 253 11 2 3 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 33 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 33 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 253 (accept_3_3 20 33 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 253 (Polychromatic418967fa.accept_16_3_1_13_1_4968 19 33
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 253
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 33 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 253 (accept_3_3 17 33 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 33 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 253 (accept_3_3 14 33 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 33 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 253
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 33 253 11 1 3 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 33 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 33 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 253 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 33 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 253 (accept_3_3 8 33 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 7
  33 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 33 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 253 (accept_3_3 5 33 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 33 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 253 (accept_3_3 2 33 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 253 (Polychromatic418967fa.accept_13_1_7_6_1_142 1 33 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 253))))))))))))))))))))))))))))))))) (allB_succ 32 253
  (allA_of_3_1 32 32 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 253 (allA_succ_of_accept 30 31 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 253 (accept_3_3 29 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 253 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 253 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 31 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 253 (accept_3_3 26 31 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 31 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 253 (accept_3_3 23 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 31 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 253 (accept_3_3 20 31 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 253 (accept_3_3 17 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 31 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 253 (accept_3_3 14 31 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 253 (Polychromatic418967fa.accept_19_13_12_6_1_11362 13 31 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 253 (accept_3_3 11 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 31 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 253 (accept_3_3 8 31 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 253 (accept_3_3 5 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  253 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 31 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 31 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 253 (accept_3_3 2 31 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 253 (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 31 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 253))))))))))))))))))))))))))))))) (allB_succ 30 253
  (allA_succ_of_accept 29 30 253 (accept_3_3 29 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 253 (Polychromatic418967fa.accept_13_2_4_6_1_2356 28 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 253 (accept_3_3 26 30 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 30 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 253
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 253 (accept_3_3 23 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 253 (Polychromatic418967fa.accept_18_3_12_1_1_3787 21 30 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 253 (accept_3_3 20 30 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 253
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 253 (accept_3_3 17 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 253 (accept_3_3 14 30 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 30 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 253
  (Polychromatic418967fa.accept_20_12_10_13_1_9747 12 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 30 253 (accept_3_3 11 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 30 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 253 (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 30 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 253 (accept_3_3 8 30 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 253
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 253 (accept_3_3 5 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  253 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 30 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 30 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 253 (accept_3_3 2 30 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 30 253 (Polychromatic418967fa.accept_16_1_14_13_1_3834 1 30 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 253)))))))))))))))))))))))))))))) (allB_succ 29 253 (allA_of_3_1
  29 29 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 253 (allA_succ_of_accept 27 28 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 253 (accept_3_3 26 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 253 (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 28 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 253 (accept_3_3 23 28 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 28
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 253 (accept_3_3 20 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 253 (Polychromatic418967fa.accept_21_19_7_1_1_3329 19 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 253 (Polychromatic418967fa.accept_19_18_9_6_1_5815 18 28 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 253 (accept_3_3 17 28 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 28 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 253 (accept_3_3 14 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 253 (Polychromatic418967fa.accept_17_13_11_15_1_5556 13 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 253 (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 28 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 253 (accept_3_3 11 28 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 253 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 28
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 253 (accept_3_3 8 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  253 (Polychromatic418967fa.accept_22_7_6_11_1_13808 7 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 28 253 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 28 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 253 (accept_3_3 5 28 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 253 (Polychromatic418967fa.accept_13_4_2_6_1_1043 4 28 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 253 (accept_3_3 2 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28
  253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 28 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 253)))))))))))))))))))))))))))) (allB_succ 27 253 (allA_succ_of_accept 26 27 253 (accept_3_3 26 27 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 253 (Polychromatic418967fa.accept_10_5_7_3_1_561
  25 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 253
  (Polychromatic418967fa.accept_10_4_7_3_1_54 24 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 253 (accept_3_3 23 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  27 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 253 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 27 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 253 (accept_3_3 20 27 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 253 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 27 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 253 (accept_3_3 17 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  27 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 253 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 27 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 253 (accept_3_3 14 27 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 253 (Polychromatic418967fa.accept_19_13_8_6_1_7195 13 27 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 253 (accept_3_3 11 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 27 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 253 (accept_3_3 8 27 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 253 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 27 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 253 (accept_3_3 5 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 27 253 (Polychromatic418967fa.accept_13_3_1_6_1_509 3 27 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 253 (accept_3_3 2 27 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 27 253 (Polychromatic418967fa.accept_15_1_12_13_1_944 1 27 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 253))))))))))))))))))))))))))) (allB_succ 26 253 (allA_of_3_1 26
  26 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 253 (allA_succ_of_accept 24 25 253
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 25 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 253 (accept_3_3 23 25 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 25 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 25 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 253 (accept_3_3 20 25 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 253 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 25 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 253
  (Polychromatic418967fa.accept_10_8_5_3_1_543 18 25 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 253 (accept_3_3 17 25 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 25 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 253 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 25 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 253 (accept_3_3 14 25 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 25 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 253 (accept_3_3 11 25 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 25 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 253 (Polychromatic418967fa.accept_22_9_3_11_1_15411 9 25 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 253 (accept_3_3 8 25 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 253 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 25 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 253
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 25 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 253 (accept_3_3 5 25 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  253 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 25 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 25 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 253 (accept_3_3 2 25 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 253 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 25 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 253))))))))))))))))))))))))) (allB_succ 24 253
  (allA_succ_of_accept 23 24 253 (accept_3_3 23 24 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  24 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 24 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 24 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 253 (accept_3_3 20 24 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 253 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 24 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 253
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 24 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 253 (accept_3_3 17 24 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 24 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 253 (Polychromatic418967fa.accept_19_15_5_6_1_5760 15 24 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 253 (accept_3_3 14 24 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 24 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 253
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 24 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 253 (accept_3_3 11 24 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 253 (Polychromatic418967fa.accept_21_10_3_1_1_3323 10 24 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 253 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 253 (accept_3_3 8 24 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 253 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 253
  (Polychromatic418967fa.accept_21_6_3_1_1_6286 6 24 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 253 (accept_3_3 5 24 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  253 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 24 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 253 (accept_3_3 2 24 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 253 (Polychromatic418967fa.accept_19_1_5_6_1_5811 1 24 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 253)))))))))))))))))))))))) (allB_succ 23 253 (allA_of_3_1 23 23
  253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 253 (allA_succ_of_accept 21 22 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 253 (accept_3_3 20 22 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 253 (Polychromatic418967fa.accept_19_18_3_6_1_9989 18 22 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 253 (accept_3_3 17 22 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 22 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 253
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 253 (accept_3_3 14 22 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 253 (Polychromatic418967fa.accept_17_13_5_15_1_8103 13 22 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 22 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 22 253 11 1 2 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 22 253 (Polychromatic418967fa.accept_13_10_9_6_1_1026
  10 22 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 253 (accept_3_3 8 22 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 253 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 22 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 253 (accept_3_3 5 22 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 253 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 22 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 253 (accept_3_3 2 22 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 253 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1
  22 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 253)))))))))))))))))))))) (allB_succ
  21 253 (allA_succ_of_accept 20 21 253 (accept_3_3 20 21 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 253 (Polychromatic418967fa.accept_15_4_6_13_1_956 19 21 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 253 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 21 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 253 (accept_3_3 17 21 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  21 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 253
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 21 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 253 (accept_3_3 14 21 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 253 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 21 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 253 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 21 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 253 (accept_3_3 11 21 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 21 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 253
  (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 21 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 253 (accept_3_3 8 21 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  253 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 21 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 253 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 21 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 253 (accept_3_3 5 21 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 253 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  21 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 253 (accept_3_3 2 21 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 253 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1
  21 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 253))))))))))))))))))))) (allB_succ
  20 253 (allA_of_3_1 20 20 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 253 (allA_succ_of_accept 18 19
  253 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 253 (accept_3_3 17 19 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 253 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 19 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 253 (Polychromatic418967fa.accept_16_15_3_13_1_2818 15 19 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 253 (accept_3_3 14 19 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 253 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 19 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 253
  (Polychromatic418967fa.accept_20_12_19_13_1_6776 12 19 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 19 253 (accept_3_3 11 19 253 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 19 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 253 (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 19 253
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 253 (accept_3_3 8 19 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 253 (Polychromatic418967fa.accept_17_7_2_15_1_1255
  7 19 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 253 (accept_3_3 5 19 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  253 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 19 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 19 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 253 (accept_3_3 2 19 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 253 (Polychromatic418967fa.accept_16_1_3_13_1_2785 1 19 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 253))))))))))))))))))) (allB_succ 18 253 (allA_succ_of_accept 17
  18 253 (accept_3_3 17 18 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 253
  (Polychromatic418967fa.accept_10_6_8_3_1_930 16 18 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 253 (accept_3_3 14 18 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 253 (Polychromatic418967fa.accept_26_13_18_19_1_15410 13 18 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 253
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 18 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 18 253 (accept_3_3 11 18 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  18 253 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 18 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 18 253 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 18 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 253 (accept_3_3 8 18 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 253
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 18 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 253 (accept_3_3 5 18 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18
  253 (Polychromatic418967fa.accept_13_4_5_6_1_3201 4 18 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 253 (accept_3_3 2 18 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 253 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 18 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 253)))))))))))))))))) (allB_succ 17 253 (allA_of_3_1
  17 17 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 253 (allA_succ_of_accept 15 16 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 253 (accept_3_3 14 16 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 16 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 16 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 253 (accept_3_3 11 16 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 16 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 253 (accept_3_3 8 16 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  253 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 16 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 16 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 253 (accept_3_3 5 16 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 253 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 16 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 253 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 253 (accept_3_3 2 16 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 253 (Polychromatic418967fa.accept_13_1_3_6_1_158 1
  16 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 253)))))))))))))))) (allB_succ 15 253
  (allA_succ_of_accept 14 15 253 (accept_3_3 14 15 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  15 253 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 15 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 15 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 253 (accept_3_3 11 15 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 253
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 15 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 253 (accept_3_3 8 15 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  253 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 15 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 15 253 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 253 (accept_3_3 5 15 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 15 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 253 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 15
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 253 (accept_3_3 2 15 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 253 (Polychromatic418967fa.accept_13_1_2_6_1_515 1
  15 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 253))))))))))))))) (allB_succ 14 253
  (allA_of_3_1 14 14 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 253 (allA_succ_of_accept 12 13 253
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 253 (accept_3_3 11 13 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 253 (Polychromatic418967fa.accept_18_10_13_1_1_7736 10 13 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 253 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 13 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 253 (accept_3_3 8 13 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 253 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 13 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 253
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 13 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 253 (accept_3_3 5 13 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  253 (Polychromatic418967fa.accept_19_4_13_6_1_8671 4 13 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 253 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 13 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 253 (accept_3_3 2 13 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 253 (Polychromatic418967fa.accept_25_1_13_3_1_15409 1 13 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 253))))))))))))) (allB_succ 12 253
  (allA_succ_of_accept 11 12 253 (accept_3_3 11 12 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  12 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 12 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 12 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 253 (accept_3_3 8 12 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 253 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 253
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 12 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 253 (accept_3_3 5 12 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12
  253 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 12 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 12 253 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 253 (accept_3_3 2 12 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 12 253 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 12 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 253)))))))))))) (allB_succ 11 253 (allA_of_3_1 11 11 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 253 (allA_succ_of_accept 9 10 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 253 (accept_3_3 8 10 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  253 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 253 (Polychromatic418967fa.accept_25_6_10_3_1_15408 6 10 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 253 (accept_3_3 5 10 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 253 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 10 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 253 (accept_3_3 2 10 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 253 (Polychromatic418967fa.accept_15_1_10_13_1_939
  1 10 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 253)))))))))) (allB_succ 9 253
  (allA_succ_of_accept 8 9 253 (accept_3_3 8 9 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 253
  (Polychromatic418967fa.accept_13_7_9_6_1_148 7 9 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 253 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 9 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 253 (accept_3_3 5 9 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 253 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 253 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 9
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 253 (accept_3_3 2 9 253
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 253 (Polychromatic418967fa.accept_13_1_9_6_1_146 1 9
  253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 253))))))))) (allB_succ 8 253
  (allA_of_3_1 8 8 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 253 (allA_succ_of_accept 6 7 253
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 253 (accept_3_3 5 7 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 253
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 253 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 7 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 253 (accept_3_3 2 7 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 253 (Polychromatic418967fa.accept_13_1_7_6_1_142 1 7 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 253))))))) (allB_succ 6 253 (allA_succ_of_accept 5 6 253
  (accept_3_3 5 6 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 253
  (Polychromatic418967fa.accept_9_4_6_1_1_393 4 6 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 253 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 253 (accept_3_3 2 6 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 253 (Polychromatic418967fa.accept_25_1_6_3_1_15407 1 6 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 253)))))) (allB_succ 5 253 (allA_of_3_1 5 5 253 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 253 (allA_succ_of_accept 3 4 253
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 253 (accept_3_3 2 4 253 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 253
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 4 253 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 253)))) (allB_succ 3 253 (allA_succ_of_accept 2 3 253 (accept_3_3 2 3 253 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 253 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 3 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 253))) (allB_succ 2 253 (allA_of_3_1 2 2 253 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


