-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch263_Segment000
-- name    : Polychromatic418967fa_Branch263_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:45:48.335325+00:00
-- url     : https://prove2.me/theorems/f6002b68-6ed1-4e77-97d7-ab93be2e4383
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

def Polychromatic418967fa.branch_263_segment_000 : allB 123 263 :=
  allB_succ 122 263 (allA_succ_of_accept 121 122 263 (accept_3_2 121 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 122 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 120 122 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 122 263 (Polychromatic418967fa.accept_11_9_1_10_1_920 119 122
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 122 263 (accept_3_2 118 122
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 122 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 122 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 116 122 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 122 263 (accept_3_2 115 122 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 122 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 114 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 122 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 122 263 (accept_3_2 112 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 122 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 111 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 122 263 (Polychromatic418967fa.accept_13_6_5_3_1_426 110 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 122 263 (accept_3_2 109 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 122 263 (Polychromatic418967fa.accept_11_9_1_10_1_920 108 122
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 122 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 107 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 122 263 (accept_3_2 106 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 122 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 104 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 122 263 (accept_3_2 103 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 122 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 102 122
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 122 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 122 263 (accept_3_2 100 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 122 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 122 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 98 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 122 263 (accept_3_2 97 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 122 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 96 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 122 263
  (Polychromatic418967fa.accept_10_5_2_3_1_239 95 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 122 263 (accept_3_2 94 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 122 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 92 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 122 263 (accept_3_2 91 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 122 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 122 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 122 263 (accept_3_2 88 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 122 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 122 263 (Polychromatic418967fa.accept_11_9_1_10_1_920 86 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 122 263 (accept_3_2 85 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 122 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 122 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 122 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 83 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 122 263 (accept_3_2 82 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 122 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 122 263 (accept_3_2 79 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 122 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 122 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 122 263 (accept_3_2 76 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 122 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 122 263 (Polychromatic418967fa.accept_13_9_5_3_1_428 74 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 122 263 (accept_3_2 73 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 122 263 (Polychromatic418967fa.accept_19_15_8_16_1_10745 72
  122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 122 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 71 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 122 263 (accept_3_2 70 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 122 263 (Polychromatic418967fa.accept_11_2_1_10_1_196 68 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 122 263 (accept_3_2 67 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 122 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 122 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 122 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 122 263 (accept_3_2 64 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 122 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 122 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 122 263 (accept_3_2 61 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 122 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 122 263
  (Polychromatic418967fa.accept_18_5_14_11_1_2073 59 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 122 263 (accept_3_2 58 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 122 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 122 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 56 122
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 122 263 (accept_3_2 55 122
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 122 263
  (Polychromatic418967fa.accept_13_2_5_3_1_406 54 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 122 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 122 263 (accept_3_2 52 122 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 122 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 263 (Polychromatic418967fa.accept_7_1_3_4_1_128
  50 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 122 263 (accept_3_2 49
  122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 122 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 122 263 (Polychromatic418967fa.accept_13_8_5_3_1_427 47 122 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 263 (accept_3_2 46 122 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 263 (Polychromatic418967fa.accept_9_8_5_2_1_422
  44 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 122 263 (accept_3_2 43
  122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 122 263
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 263 (accept_3_2 40 122 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 122 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 263
  (Polychromatic418967fa.accept_18_2_14_11_1_3139 38 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 122 263 (accept_3_2 37 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 122 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 122 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 122 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 263 (accept_3_2 34 122 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 263 (accept_3_2 31 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 263 (accept_3_2 28 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 122 263 (accept_3_2 25 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 122 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 122 263 (Polychromatic418967fa.accept_18_5_14_11_1_2073 23 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 263 (accept_3_2 22 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 263 (accept_3_2 19 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 263 (Polychromatic418967fa.accept_19_18_8_16_1_9331 18 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 263 (accept_3_2 16 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 263
  (Polychromatic418967fa.accept_13_1_5_3_1_888 14 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 263 (accept_3_2 13 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 263 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 263 (accept_3_2 10 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 263 (accept_3_2 7 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 263 (accept_3_2 4 122 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 122 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 263
  (Polychromatic418967fa.accept_11_2_1_10_1_196 2 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 263 (accept_3_2 1 122 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 263 (allA_of_3_0 121 121 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 263
  (allA_succ_of_accept 119 120 263 (Polychromatic418967fa.accept_22_9_10_21_1_12997 119 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 120 263 (accept_3_2 118 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 117 120 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 117 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 120 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 116 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 120 263 (accept_3_2 115 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 120 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 114 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 120 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 113 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 120 263 (accept_3_2 112 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 120 263 (Polychromatic418967fa.accept_16_15_8_7_1_3407 111
  120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 120 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 110 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 120 263 (accept_3_2 109 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 120 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 108 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 120 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 107 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 120 263 (accept_3_2 106 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 120 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 105 120
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 120 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 104 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 120 263 (accept_3_2 103 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 120 263 (Polychromatic418967fa.accept_14_4_8_11_1_794 102 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 120 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 101 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 120 263 (accept_3_2 100 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 120 263 (Polychromatic418967fa.accept_18_9_12_11_1_5642 99 120
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 120 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 98 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 120 263 (accept_3_2 97 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 120 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 120 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 95 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 120 263 (accept_3_2 94 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 120 263 (Polychromatic418967fa.accept_21_9_15_11_1_7018 93 120 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 120 263
  (Polychromatic418967fa.accept_16_12_8_7_1_4530 92 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 120 263 (accept_3_2 91 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 120 263 (Polychromatic418967fa.accept_21_6_15_11_1_5410 90 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 120 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 89 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 120 263 (accept_3_2 88 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 120 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 120 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 86 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 120 263 (accept_3_2 85 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 120 263 (Polychromatic418967fa.accept_16_4_8_7_1_3396 84 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 120 263 (Polychromatic418967fa.accept_19_7_6_16_1_3818 83 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 120 263 (accept_3_2 82 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 120 263 (Polychromatic418967fa.accept_16_1_8_7_1_3377 81 120
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 120 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 120 263 (accept_3_2 79 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 120 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 120 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 120 263 (accept_3_2 76 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 120 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 120 263
  (Polychromatic418967fa.accept_14_4_8_11_1_794 74 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 120 263 (accept_3_2 73 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 120 263 (Polychromatic418967fa.accept_17_4_1_8_1_5070 72 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 120 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 120 263 (accept_3_2 70 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 120 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 120 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 120 263 (accept_3_2 67 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 120 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 120 263 (Polychromatic418967fa.accept_16_1_8_7_1_3377 65 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 120 263 (accept_3_2 64 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 120 263 (Polychromatic418967fa.accept_16_15_8_7_1_3407 63 120
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 120 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 120 263 (accept_3_2 61 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 120 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 120 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 263 (accept_3_2 58 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 120 263 (Polychromatic418967fa.accept_16_9_8_7_1_4529 57 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 120 263
  (Polychromatic418967fa.accept_25_6_20_13_1_16064 56 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 120 263 (accept_3_2 55 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 120 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 120 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 120 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 120 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 263 (accept_3_2 52 120 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 120 263 (Polychromatic418967fa.accept_9_6_3_2_1_431
  51 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 120 263 (accept_3_2 49 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 120 263 (Polychromatic418967fa.accept_19_10_6_16_1_7964 48 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 120 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 263 (accept_3_2 46 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 120 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 263 (accept_3_2 43 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 120 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 120 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 263 (accept_3_2 40 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 263 (Polychromatic418967fa.accept_22_17_10_21_1_16076 39 120 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 120 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 263 (accept_3_2 37 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 120 263 (Polychromatic418967fa.accept_16_4_8_7_1_3396 36 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 120 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 263 (accept_3_2 34 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 120 263 (accept_3_2 31 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 120 263 (Polychromatic418967fa.accept_19_11_6_16_1_3805 30 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 120 263 (Polychromatic418967fa.accept_19_10_6_16_1_7964 29 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 263 (accept_3_2 28 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 263 (Polychromatic418967fa.accept_18_9_12_11_1_5642 27 120
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 120 263 (accept_3_2 25 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 120 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 120 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 263 (accept_3_2 22 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 263 (Polychromatic418967fa.accept_17_4_1_8_1_5070 21 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 263
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 20 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 263 (accept_3_2 19 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 120 263 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 263 (accept_3_2 16 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 263 (accept_3_2 13 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 120 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 120 263 (Polychromatic418967fa.accept_17_11_1_8_1_7502 11 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 263 (accept_3_2 10 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 263 (Polychromatic418967fa.accept_16_9_8_7_1_4529 9 120 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 263 (accept_3_2 7 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 120 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 263 (accept_3_2 4 120 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 120 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 263
  (Polychromatic418967fa.accept_22_2_10_21_1_16075 2 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 120 263 (accept_3_2 1 120 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  120
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 263 (allA_succ_of_accept 118 119 263 (accept_3_2 118 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 263 (Polychromatic418967fa.accept_19_3_5_16_1_13380 117 119 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 263 (Polychromatic418967fa.accept_10_6_9_3_1_935
  116 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 263 (accept_3_2
  115 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 263
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 114 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 119 263 (Polychromatic418967fa.accept_13_9_2_3_1_3027 113 119 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 263 (accept_3_2 112 119 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 119 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 111 119 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 263
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 110 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 119 263 (accept_3_2 109 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 119 263 (Polychromatic418967fa.accept_14_10_7_11_1_3015 108 119 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 263
  (Polychromatic418967fa.accept_11_8_9_10_1_503 107 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 119 263 (accept_3_2 106 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 119 263 (Polychromatic418967fa.accept_13_1_2_3_1_911 105 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 119 263 (Polychromatic418967fa.accept_10_4_9_3_1_1907 104 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 119 263 (accept_3_2 103 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 119 263 (Polychromatic418967fa.accept_13_11_2_3_1_883 102 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 119 263
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 101 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 119 263 (accept_3_2 100 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 119 263 (Polychromatic418967fa.accept_15_9_14_8_1_1396 99 119 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 263 (Polychromatic418967fa.accept_19_3_5_16_1_13380 98 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 119 263 (accept_3_2 97 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 119 263
  (Polychromatic418967fa.accept_10_6_9_3_1_935 96 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 119 263 (Polychromatic418967fa.accept_15_5_14_8_1_1376 95 119 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 263 (accept_3_2 94 119 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 119 263 (Polychromatic418967fa.accept_27_12_11_20_1_12226 93 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 263
  (Polychromatic418967fa.accept_13_1_2_3_1_911 92 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 263 (accept_3_2 91 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 263 (Polychromatic418967fa.accept_13_12_2_3_1_1527 90 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 89 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 263 (accept_3_2 88 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 263 (Polychromatic418967fa.accept_13_9_2_3_1_3027 87 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 263
  (Polychromatic418967fa.accept_10_6_9_3_1_935 86 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 263 (accept_3_2 85 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 119 263 (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 119 263 (Polychromatic418967fa.accept_13_5_2_3_1_1526 83 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 263 (accept_3_2 82 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 263 (Polychromatic418967fa.accept_15_6_14_8_1_245 81 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 263
  (Polychromatic418967fa.accept_14_10_7_11_1_3015 80 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 119 263 (accept_3_2 79 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 119 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 78 119 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 263 (Polychromatic418967fa.accept_13_12_2_3_1_1527 77 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 263 (accept_3_2 76 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 263
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 75 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 119 263 (Polychromatic418967fa.accept_10_4_9_3_1_1907 74 119 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 263 (accept_3_2 73 119 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 119 263 (Polychromatic418967fa.accept_27_18_11_20_1_4405 72 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 263
  (Polychromatic418967fa.accept_19_14_5_16_1_7940 71 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 119 263 (accept_3_2 70 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 119 263 (Polychromatic418967fa.accept_15_9_14_8_1_1396 69 119 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 263 (Polychromatic418967fa.accept_19_11_5_16_1_1456 68 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 263 (accept_3_2 67 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 119 263
  (Polychromatic418967fa.accept_10_6_9_3_1_935 66 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 119 263 (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 119 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 263 (accept_3_2 64 119 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 119 263 (Polychromatic418967fa.accept_11_8_9_10_1_503 63 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 263
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 62 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 263 (accept_3_2 61 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 263 (Polychromatic418967fa.accept_14_4_7_11_1_790 60 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 263 (Polychromatic418967fa.accept_14_3_7_11_1_765 59 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 263 (accept_3_2 58 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 263 (Polychromatic418967fa.accept_13_5_2_3_1_1526 57 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 263
  (Polychromatic418967fa.accept_10_6_9_3_1_935 56 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 263 (accept_3_2 55 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 263 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 263 (Polychromatic418967fa.accept_13_1_2_3_1_911 53 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 263 (accept_3_2 52 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 263 (Polychromatic418967fa.accept_13_12_2_3_1_1527 51 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 263
  (Polychromatic418967fa.accept_13_11_2_3_1_883 50 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 263 (accept_3_2 49 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 263 (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 263 (Polychromatic418967fa.accept_21_5_14_11_1_10102 47 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 263 (accept_3_2 46 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 45 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 263
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 44 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 263 (accept_3_2 43 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 263 (Polychromatic418967fa.accept_20_2_19_3_1_10530 42 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 263 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 263 (accept_3_2 40 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 263 (Polychromatic418967fa.accept_15_9_14_8_1_1396 39 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 263
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 38 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 263 (accept_3_2 37 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 263 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 263 (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 263 (accept_3_2 34 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 263 (Polychromatic418967fa.accept_19_14_5_16_1_7940 33 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 263
  (Polychromatic418967fa.accept_14_4_7_11_1_790 32 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 263 (accept_3_2 31 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 263 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 263 (Polychromatic418967fa.accept_19_10_5_16_1_6522 29 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 263 (accept_3_2 28 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 263 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 263
  (Polychromatic418967fa.accept_10_6_9_3_1_935 26 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 263 (accept_3_2 25 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 263 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 263 (accept_3_2 22 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 263 (Polychromatic418967fa.accept_15_6_14_8_1_245 21 119
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 263
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 263 (accept_3_2 19 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 263 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 263 (Polychromatic418967fa.accept_14_3_7_11_1_765 17 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 263 (accept_3_2 16 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 263 (Polychromatic418967fa.accept_25_15_19_13_1_1932 15
  119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 263
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 263 (accept_3_2 13 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 263 (Polychromatic418967fa.accept_13_11_2_3_1_883 11 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 263 (accept_3_2 10 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 263 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 119 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 263
  (Polychromatic418967fa.accept_11_8_9_10_1_503 8 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 263 (accept_3_2 7 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 263 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 263 (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 119 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 263 (accept_3_2 4 119 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 263 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 119 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 263
  (Polychromatic418967fa.accept_19_2_5_16_1_7986 2 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 263 (accept_3_2 1 119 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 263 (allA_of_3_0 118 118 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 263
  (allA_succ_of_accept 116 117 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 117 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 263 (accept_3_2 115 117 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 113 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 263 (accept_3_2 112 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 111 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 263 (accept_3_2 109 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 263 (Polychromatic418967fa.accept_15_3_12_8_1_738 108 117
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 107 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 263 (accept_3_2 106 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 117 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 105 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 117 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 263 (accept_3_2 103 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 117
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 263
  (Polychromatic418967fa.accept_15_11_12_8_1_739 101 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 117 263 (accept_3_2 100 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 117 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 99 117 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 117 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 263 (accept_3_2 97 117 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 263 (Polychromatic418967fa.accept_10_6_7_3_1_547
  96 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 95 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 263 (accept_3_2 94 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 117 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 117 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 263 (accept_3_2 91 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 263
  (Polychromatic418967fa.accept_19_13_3_16_1_6467 89 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 117 263 (accept_3_2 88 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 117 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 87 117 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 117 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 263 (accept_3_2 85 117 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 263 (Polychromatic418967fa.accept_10_4_7_3_1_54
  84 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 117 263 (accept_3_2 82 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 117 263 (Polychromatic418967fa.accept_17_13_15_8_1_3860 81 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 117 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 263 (accept_3_2 79 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 263
  (Polychromatic418967fa.accept_19_1_3_16_1_9413 77 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 263 (accept_3_2 76 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 117 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 75 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 263 (accept_3_2 73 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 263 (accept_3_2 70 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 117 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 263 (accept_3_2 67 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 263 (accept_3_2 64 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 117 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 263 (accept_3_2 61 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 263 (Polychromatic418967fa.accept_16_12_5_7_1_2360 60 117 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 263
  (Polychromatic418967fa.accept_16_11_5_7_1_2395 59 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 263 (accept_3_2 58 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 117 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 117 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 263 (accept_3_2 55 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 263
  (Polychromatic418967fa.accept_19_15_3_16_1_9382 53 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 117 263 (accept_3_2 52 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 117 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 117 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 117 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 263 (accept_3_2 49 117 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 263 (Polychromatic418967fa.accept_7_6_5_4_1_297
  48 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 263
  (Polychromatic418967fa.accept_11_3_7_10_1_180 47 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 263 (accept_3_2 46 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 263 (accept_3_2 43 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 263 (accept_3_2 40 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 263 (accept_3_2 37 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 263 (accept_3_2 34 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 263 (Polychromatic418967fa.accept_15_3_12_8_1_738 33 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 263 (accept_3_2 31 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 263 (accept_3_2 28 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 263 (accept_3_2 25 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 263 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 263 (accept_3_2 22 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 263 (Polychromatic418967fa.accept_19_2_3_16_1_6469 21 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 263 (accept_3_2 19 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 263
  (Polychromatic418967fa.accept_19_17_3_16_1_13384 17 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 117 263 (accept_3_2 16 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 117 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 117 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 263 (accept_3_2 13 117 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 263
  (Polychromatic418967fa.accept_16_12_5_7_1_2360 12 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 263 (Polychromatic418967fa.accept_15_11_12_8_1_739 11 117 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 263 (accept_3_2 10 117 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8
  117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 263 (accept_3_2 7 117
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27
  6 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 263 (accept_3_2 4 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 263 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 117 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 263 (accept_3_2 1 117 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 263 (allA_succ_of_accept 115 116 263 (accept_3_2 115 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 116 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 114 116 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 116 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 113 116
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 116 263 (accept_3_2 112 116
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 116 263
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 116 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 110 116 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 116 263 (accept_3_2 109 116 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 116 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 108 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 116 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 107 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 116 263 (accept_3_2 106 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 116 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 104 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 116 263 (accept_3_2 103 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 116 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 102 116
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 116 263
  (Polychromatic418967fa.accept_17_16_14_8_1_7608 101 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 116 263 (accept_3_2 100 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 116 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 116 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 98 116
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 116 263 (accept_3_2 97 116
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 116 263
  (Polychromatic418967fa.accept_9_6_8_2_1_410 96 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 116 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 116 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 116 263 (accept_3_2 94 116 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 116 263
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 92 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 116 263 (accept_3_2 91 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 116 263 (Polychromatic418967fa.accept_19_14_2_16_1_6484 90 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 116 263 (Polychromatic418967fa.accept_10_9_6_3_1_545 89 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 116 263 (accept_3_2 88 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 116 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 116 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 86 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 116 263 (accept_3_2 85 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 116 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 116 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 116 263 (accept_3_2 82 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 116 263
  (Polychromatic418967fa.accept_13_2_12_3_1_415 80 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 116 263 (accept_3_2 79 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 116 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 116 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 116 263 (accept_3_2 76 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 116 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 116 263 (accept_3_2 73 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 116 263 (Polychromatic418967fa.accept_15_12_11_8_1_1392 72 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 116 263 (Polychromatic418967fa.accept_11_5_6_10_1_1432 71 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 116 263 (accept_3_2 70 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 116 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 116 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 116 263 (accept_3_2 67 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 116 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 116 263 (Polychromatic418967fa.accept_15_5_11_8_1_1391 65 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 116 263 (accept_3_2 64 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 116 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 116 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 116 263 (accept_3_2 61 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 116 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 116 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 116 263 (accept_3_2 58 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 116 263
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 56 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 116 263 (accept_3_2 55 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 116 263 (Polychromatic418967fa.accept_13_2_12_3_1_415 54 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 116 263 (Polychromatic418967fa.accept_20_13_16_3_1_4479 53 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 116 263 (accept_3_2 52 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 116 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 116 263 (accept_3_2 49 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 116 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 116 263 (Polychromatic418967fa.accept_10_7_6_3_1_927 47 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 116 263 (accept_3_2 46 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 116 263
  (Polychromatic418967fa.accept_16_12_4_7_1_3391 44 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 116 263 (accept_3_2 43 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 116 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 116 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 116 263 (accept_3_2 40 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 116 263
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 116 263 (accept_3_2 37 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 116 263 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 116 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 116 263 (accept_3_2 34 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 116 263 (accept_3_2 31 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 116 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 116 263 (Polychromatic418967fa.accept_10_9_6_3_1_545 29 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 263 (accept_3_2 28 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 116 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 116 263 (accept_3_2 25 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 116 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 116 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 263 (accept_3_2 22 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 263
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 20 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 116 263 (accept_3_2 19 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 116 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 116 263 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 263 (accept_3_2 16 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 116 263 (accept_3_2 13 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 116 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 116 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 263 (accept_3_2 10 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 263
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 263 (accept_3_2 7 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 263 (accept_3_2 4 116 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 263 (accept_3_2 1 116 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 263 (allA_of_3_0 115 115 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 263
  (allA_succ_of_accept 113 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 113 114 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 114 263 (accept_3_2 112 114 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 114 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 111 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 114 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 110 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 114 263 (accept_3_2 109 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 114 263 (Polychromatic418967fa.accept_15_3_9_8_1_3164 108 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 114 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 107 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 114 263 (accept_3_2 106 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 114 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 114 263
  (Polychromatic418967fa.accept_7_6_2_4_1_291 104 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 114 263 (accept_3_2 103 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 114 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 114 263 (accept_3_2 100 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 114 263 (Polychromatic418967fa.accept_10_9_4_3_1_539 99 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 114 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 98 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 114 263 (accept_3_2 97 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 114 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 114 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 95 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 114 263 (accept_3_2 94 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 114 263
  (Polychromatic418967fa.accept_15_2_9_8_1_736 92 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 114 263 (accept_3_2 91 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 114 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 114 263 (accept_3_2 88 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 114 263 (Polychromatic418967fa.accept_10_7_4_3_1_560 87 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 114 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 86 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 114 263 (accept_3_2 85 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 114 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 114 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 114 263 (accept_3_2 82 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 114 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 80 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 114 263 (accept_3_2 79 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 114 263 (Polychromatic418967fa.accept_15_3_9_8_1_3164 78 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 263 (accept_3_2 76 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 114 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 114 263
  (Polychromatic418967fa.accept_15_14_9_8_1_3165 74 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 114 263 (accept_3_2 73 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 114 263 (Polychromatic418967fa.accept_13_7_10_3_1_1505 72 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 114 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 263 (accept_3_2 70 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 114 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 114 263 (accept_3_2 67 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 114 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 263 (accept_3_2 64 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 114 263 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 114 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 114 263
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 114 263 (accept_3_2 61 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 114 263 (Polychromatic418967fa.accept_11_5_4_10_1_524 60 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 114 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 263 (accept_3_2 58 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 263
  (Polychromatic418967fa.accept_17_5_12_8_1_6304 56 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 114 263 (accept_3_2 55 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 114 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 263 (accept_3_2 52 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 114 263 (Polychromatic418967fa.accept_14_9_2_11_1_780 51 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 114 263 (accept_3_2 49 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 114 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 114 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 263 (accept_3_2 46 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 114 263 (accept_3_2 43 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 114 263 (Polychromatic418967fa.accept_22_20_4_21_1_8237 42 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 263 (accept_3_2 40 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 263
  (Polychromatic418967fa.accept_11_5_4_10_1_524 38 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 114 263 (accept_3_2 37 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 114 263 (Polychromatic418967fa.accept_21_15_9_11_1_5417 36 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 114 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 263 (accept_3_2 34 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 114 263 (accept_3_2 31 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 114 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 263 (accept_3_2 28 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 114 263 (accept_3_2 25 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 114 263 (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 114 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 263 (accept_3_2 22 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 263
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 114 263 (accept_3_2 19 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 114 263 (Polychromatic418967fa.accept_15_3_9_8_1_3164 18 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 263 (accept_3_2 16 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 263 (Polychromatic418967fa.accept_13_2_10_3_1_1538 15 114 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 263 (accept_3_2 13 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 114 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 114 263 (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 263 (accept_3_2 10 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 263 (accept_3_2 7 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  114 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 114 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 263 (accept_3_2 4 114 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 114 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 263
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 263 (accept_3_2 1 114 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 263 (allA_succ_of_accept 112 113 263 (accept_3_2 112 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 111 113 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 113
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 263 (accept_3_2 109 113
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 108 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 107 113 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 263 (accept_3_2 106 113 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 105 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 263
  (Polychromatic418967fa.accept_16_8_1_7_1_2355 104 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 263 (accept_3_2 103 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 101 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 263 (accept_3_2 100 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 263 (Polychromatic418967fa.accept_13_8_9_3_1_2213 99 113
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 263 (accept_3_2 97 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 263 (Polychromatic418967fa.accept_11_7_3_10_1_1461 95 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 263 (accept_3_2 94 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 93 113 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 263
  (Polychromatic418967fa.accept_20_12_13_3_1_13299 92 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 113 263 (accept_3_2 91 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 113 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 113 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 113 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 89 113 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 263 (accept_3_2 88 113 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 263 (Polychromatic418967fa.accept_7_3_1_4_1_121
  87 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 263 (accept_3_2 85 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 263 (Polychromatic418967fa.accept_13_5_9_3_1_870 83 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 263 (accept_3_2 82 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 263 (Polychromatic418967fa.accept_20_1_13_3_1_11838 81 113
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 263 (accept_3_2 79 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 263 (Polychromatic418967fa.accept_13_12_9_3_1_3047 77 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 263 (accept_3_2 76 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 113 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 263 (accept_3_2 73 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 263 (Polychromatic418967fa.accept_13_7_9_3_1_1504 72 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 263 (accept_3_2 70 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 263 (accept_3_2 67 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 263 (Polychromatic418967fa.accept_17_14_11_8_1_3854 65 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 263 (accept_3_2 64 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 263 (Polychromatic418967fa.accept_29_5_26_2_1_16074 63 113
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 263 (accept_3_2 61 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 263 (accept_3_2 58 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 263
  (Polychromatic418967fa.accept_16_8_1_7_1_2355 56 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 263 (accept_3_2 55 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 263 (accept_3_2 52 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 263 (accept_3_2 49 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 263 (accept_3_2 46 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 263 (accept_3_2 43 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 263 (Polychromatic418967fa.accept_13_2_9_3_1_2212 41 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 263 (accept_3_2 40 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 113 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 263 (accept_3_2 37 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 263 (Polychromatic418967fa.accept_17_2_11_8_1_2726 36 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 263 (accept_3_2 34 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 263
  (Polychromatic418967fa.accept_13_6_9_3_1_915 32 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 263 (accept_3_2 31 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 263 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 263 (accept_3_2 28 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 263 (Polychromatic418967fa.accept_19_8_18_16_1_7937 27 113
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 263 (accept_3_2 25 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 263 (Polychromatic418967fa.accept_27_23_5_20_1_16073 23 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 263 (accept_3_2 22 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 113 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 263
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 263 (accept_3_2 19 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 263 (accept_3_2 16 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 263 (accept_3_2 13 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 263 (Polychromatic418967fa.accept_20_11_13_3_1_7409 11 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 263 (accept_3_2 10 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 263 (Polychromatic418967fa.accept_17_9_11_8_1_5077 9 113
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 263 (accept_3_2 7 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 263 (accept_3_2 4 113 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 113 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 263 (accept_3_2 1 113 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 263 (allA_of_3_0 112 112 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 263
  (allA_succ_of_accept 110 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 110 111 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 263 (accept_3_2 109 111 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 108 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 107 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 263 (accept_3_2 106 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 105 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 263 (accept_3_2 103 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 263 (Polychromatic418967fa.accept_10_2_1_3_1_233 102 111
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 101 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 263 (accept_3_2 100 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 263 (Polychromatic418967fa.accept_13_8_7_3_1_430 99 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 263 (accept_3_2 97 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 95 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 263 (accept_3_2 94 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 263 (accept_3_2 91 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 263 (Polychromatic418967fa.accept_11_2_1_10_1_196 90 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 89 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 263 (accept_3_2 88 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 263 (accept_3_2 85 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 263 (Polychromatic418967fa.accept_17_16_9_8_1_5063 84 111 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 263
  (Polychromatic418967fa.accept_16_3_15_7_1_3417 83 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 263 (accept_3_2 82 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 263 (accept_3_2 79 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 77 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 263 (accept_3_2 76 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 263 (accept_3_2 73 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 263 (accept_3_2 70 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 263 (accept_3_2 67 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 263 (accept_3_2 64 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 263 (Polychromatic418967fa.accept_13_11_7_3_1_894 63 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 263 (accept_3_2 61 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 263 (accept_3_2 58 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 263 (Polychromatic418967fa.accept_11_2_1_10_1_196 57 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 263 (accept_3_2 55 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 263 (accept_3_2 52 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 263 (accept_3_2 49 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 263 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 263 (accept_3_2 46 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 263 (accept_3_2 43 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 263 (accept_3_2 40 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 263 (Polychromatic418967fa.accept_21_18_6_11_1_7031 39 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 263 (accept_3_2 37 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 263 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 111 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 263 (accept_3_2 34 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 263 (accept_3_2 31 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 263
  (Polychromatic418967fa.accept_15_14_6_8_1_1410 29 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 263 (accept_3_2 28 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 263 (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 263 (accept_3_2 25 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 263 (accept_3_2 22 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 263 (accept_3_2 19 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 263 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 263 (accept_3_2 16 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 263 (accept_3_2 13 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 263
  (Polychromatic418967fa.accept_13_11_7_3_1_894 11 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 263 (accept_3_2 10 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 263 (accept_3_2 7 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 111 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 263 (accept_3_2 4 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 111 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 263 (accept_3_2 1 111 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 263 (allA_succ_of_accept 109 110 263 (accept_3_2 109 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 110 263 (Polychromatic418967fa.accept_15_3_5_8_1_1387 108 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 110 263 (Polychromatic418967fa.accept_7_2_5_4_1_115
  107 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 110 263 (accept_3_2
  106 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 110 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 105 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 110 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 104 110 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 110 263 (accept_3_2 103 110 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 110 263 (Polychromatic418967fa.accept_15_12_5_8_1_5247 102 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 110 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 110 263 (accept_3_2 100 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 110 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 110 263 (Polychromatic418967fa.accept_19_3_15_16_1_10737 98 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 110 263 (accept_3_2 97 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 110 263 (Polychromatic418967fa.accept_13_5_6_3_1_868 96 110
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 110 263
  (Polychromatic418967fa.accept_16_15_14_7_1_10555 95 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 110 263 (accept_3_2 94 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 110 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 110 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 110 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 92 110 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 110 263 (accept_3_2 91 110 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 110 263 (Polychromatic418967fa.accept_7_6_5_4_1_297
  90 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 110 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 110 263 (accept_3_2 88 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 110 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 110 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 110 263 (accept_3_2 85 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 110 263 (Polychromatic418967fa.accept_16_4_14_7_1_5641 84 110 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 110 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 110 263 (accept_3_2 82 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 110 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 110 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 80 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 110 263 (accept_3_2 79 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 110 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 110 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 110 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 110 263 (accept_3_2 76 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 110 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 110 263 (Polychromatic418967fa.accept_13_9_6_3_1_1514 74 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 110 263 (accept_3_2 73 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 110 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 110 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 110 263 (accept_3_2 70 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 110 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 110 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 68 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 263 (accept_3_2 67 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 110 263 (Polychromatic418967fa.accept_13_1_6_3_1_1547 66 110
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 110 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 110 263 (accept_3_2 64 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 110 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 110 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 110 263 (accept_3_2 61 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 110 263 (Polychromatic418967fa.accept_19_3_15_16_1_10737 60 110 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 110 263
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 59 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 110 263 (accept_3_2 58 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 110 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 110 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 56 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 110 263 (accept_3_2 55 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 110 263 (Polychromatic418967fa.accept_21_12_5_11_1_14581 54
  110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 110 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 110 263 (accept_3_2 52 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 110 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 110 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 110 263 (accept_3_2 49 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 263
  (Polychromatic418967fa.accept_16_15_14_7_1_10555 47 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 110 263 (accept_3_2 46 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 110 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 110 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 110 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 110 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 263 (accept_3_2 43 110 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 263
  (Polychromatic418967fa.accept_15_12_5_8_1_5247 42 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 110 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 110 263 (accept_3_2 40 110 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 110 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 263
  (Polychromatic418967fa.accept_21_17_5_11_1_7028 38 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 110 263 (accept_3_2 37 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 110 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 110 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 263 (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 110
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 110 263 (accept_3_2 34 110
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 263 (Polychromatic418967fa.accept_4_1_2_3_1_9
  33 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 263 (accept_3_2 31 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 110 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 110 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 263 (accept_3_2 28 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 110 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 263
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 110 263 (accept_3_2 25 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 110 263 (Polychromatic418967fa.accept_25_24_10_13_1_16072 24 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 263 (accept_3_2 22 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 110 263 (accept_3_2 19 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 110 263 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 110 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 263 (accept_3_2 16 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 110 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 263
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 14 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 110 263 (accept_3_2 13 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 110 263 (Polychromatic418967fa.accept_15_12_5_8_1_5247 12 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 110 263 (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 263 (accept_3_2 10 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 110 263 (accept_3_2 7 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 263 (accept_3_2 4 110 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 110 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 263 (accept_3_2 1 110 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 263 (allA_of_3_0 109 109 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 263
  (allA_succ_of_accept 107 108 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 107 108 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 108 263 (accept_3_2 106 108 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 108 263 (Polychromatic418967fa.accept_10_5_8_3_1_229 105 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 108 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 104 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 108 263 (accept_3_2 103 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 108 263 (Polychromatic418967fa.accept_15_12_3_8_1_5245 102 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 108 263 (Polychromatic418967fa.accept_10_1_8_3_1_947 101 108 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 108 263 (accept_3_2 100 108 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 108 263 (Polychromatic418967fa.accept_7_1_3_4_1_128
  99 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 108 263
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 98 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 108 263 (accept_3_2 97 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 108 263 (Polychromatic418967fa.accept_10_6_8_3_1_930 96 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 108 263 (Polychromatic418967fa.accept_10_5_8_3_1_229 95 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 108 263 (accept_3_2 94 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 108 263 (Polychromatic418967fa.accept_19_17_13_16_1_5118 93
  108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 108 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 92 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 108 263 (accept_3_2 91 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 108 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 108 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 89 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 108 263 (accept_3_2 88 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 108 263 (Polychromatic418967fa.accept_15_12_3_8_1_5245 87 108
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 108 263
  (Polychromatic418967fa.accept_10_6_8_3_1_930 86 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 108 263 (accept_3_2 85 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 108 263 (Polychromatic418967fa.accept_15_9_3_8_1_3155 84 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 108 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 263 (accept_3_2 82 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 108 263 (Polychromatic418967fa.accept_10_1_8_3_1_947 81 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 108 263
  (Polychromatic418967fa.accept_15_5_3_8_1_748 80 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 108 263 (accept_3_2 79 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 108 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 108 263 (Polychromatic418967fa.accept_13_12_4_3_1_1528 77 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 108 263 (accept_3_2 76 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 108 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 108 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 108 263
  (Polychromatic418967fa.accept_11_8_9_10_1_503 74 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 108 263 (accept_3_2 73 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 108 263 (Polychromatic418967fa.accept_13_7_4_3_1_3064 72 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 108 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 263 (accept_3_2 70 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 108 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 108 263
  (Polychromatic418967fa.accept_16_4_12_7_1_4475 68 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 108 263 (accept_3_2 67 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 108 263 (Polychromatic418967fa.accept_10_6_8_3_1_930 66 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 108 263 (Polychromatic418967fa.accept_10_5_8_3_1_229 65 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 263 (accept_3_2 64 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 108 263 (Polychromatic418967fa.accept_11_8_9_10_1_503 63 108
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 108 263 (accept_3_2 61 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 108 263 (Polychromatic418967fa.accept_17_9_6_8_1_6315 60 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 108 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 263 (accept_3_2 58 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 108 263
  (Polychromatic418967fa.accept_10_6_8_3_1_930 56 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 108 263 (accept_3_2 55 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 108 263 (Polychromatic418967fa.accept_15_9_3_8_1_3155 54 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 108 263 (Polychromatic418967fa.accept_13_1_4_3_1_1545 53 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 263 (accept_3_2 52 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 108 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 108 263 (accept_3_2 49 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 108 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 108 263 (Polychromatic418967fa.accept_25_22_8_13_1_12585 47 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 263 (accept_3_2 46 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 263 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 108
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 263
  (Polychromatic418967fa.accept_24_20_12_23_1_7422 44 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 108 263 (accept_3_2 43 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 108 263 (Polychromatic418967fa.accept_15_12_3_8_1_5245 42 108 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 108 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 108 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 263 (accept_3_2 40 108 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 263 (Polychromatic418967fa.accept_15_9_3_8_1_3155
  39 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 263
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 38 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 108 263 (accept_3_2 37 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 108 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 108 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 263 (accept_3_2 34 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 263 (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 263
  (Polychromatic418967fa.accept_17_15_6_8_1_6343 32 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 108 263 (accept_3_2 31 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 108 263 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 108 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 263 (accept_3_2 28 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 263
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 108 263 (accept_3_2 25 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 108 263 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 108 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 263 (accept_3_2 22 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 263 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 108
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 263 (accept_3_2 19 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 108 263 (Polychromatic418967fa.accept_16_2_12_7_1_3410 18 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 108 263 (Polychromatic418967fa.accept_19_17_13_16_1_5118 17 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 263 (accept_3_2 16 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 108 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 263
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 14 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 263 (accept_3_2 13 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 108 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 108 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 263 (accept_3_2 10 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 263 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 108 263 (accept_3_2 7 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  108 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 108 263 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 263 (accept_3_2 4 108 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 108 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 263
  (Polychromatic418967fa.accept_16_2_12_7_1_3410 2 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 263 (accept_3_2 1 108 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 263 (allA_succ_of_accept 106 107 263 (accept_3_2 106 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 105 107 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 104 107
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 263 (accept_3_2 103 107
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 263
  (Polychromatic418967fa.accept_9_3_8_2_1_162 102 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 263 (Polychromatic418967fa.accept_16_5_11_7_1_5635 101 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 263 (accept_3_2 100 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 107 263 (Polychromatic418967fa.accept_15_9_2_8_1_1379 99 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 263
  (Polychromatic418967fa.accept_16_2_11_7_1_2352 98 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 263 (accept_3_2 97 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 263 (accept_3_2 94 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 93 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 263
  (Polychromatic418967fa.accept_8_4_3_7_1_491 92 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 263 (accept_3_2 91 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 263 (accept_3_2 88 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 87 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 86 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 263 (accept_3_2 85 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 263 (accept_3_2 82 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 263 (Polychromatic418967fa.accept_15_6_2_8_1_2223 81 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 263
  (Polychromatic418967fa.accept_17_12_5_8_1_7680 80 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 263 (accept_3_2 79 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 263 (accept_3_2 76 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 263
  (Polychromatic418967fa.accept_10_4_7_3_1_54 74 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 263 (accept_3_2 73 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 263 (Polychromatic418967fa.accept_14_2_9_11_1_3054 72 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 263 (Polychromatic418967fa.accept_17_3_5_8_1_1687 71 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 263 (accept_3_2 70 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 107 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 263 (accept_3_2 67 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 65 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 263 (accept_3_2 64 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 263 (Polychromatic418967fa.accept_16_15_11_7_1_6951 63 107
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 263
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 263 (accept_3_2 61 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 263 (accept_3_2 58 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 263
  (Polychromatic418967fa.accept_10_6_7_3_1_547 56 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 263 (accept_3_2 55 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 263 (Polychromatic418967fa.accept_11_9_8_10_1_934 53 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 263 (accept_3_2 52 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 107 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 263 (accept_3_2 49 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 263 (accept_3_2 46 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 263
  (Polychromatic418967fa.accept_8_4_3_7_1_491 44 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 263 (accept_3_2 43 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 263 (accept_3_2 40 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 263
  (Polychromatic418967fa.accept_18_2_17_11_1_3178 38 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 107 263 (accept_3_2 37 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 107 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 107 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 107
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 263 (accept_3_2 34 107
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 107 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 107 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 263 (accept_3_2 31 107 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 107 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 263
  (Polychromatic418967fa.accept_17_12_5_8_1_7680 29 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 263 (accept_3_2 28 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 263 (accept_3_2 25 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 263 (accept_3_2 22 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 263 (accept_3_2 19 107 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 263 (Polychromatic418967fa.accept_16_2_11_7_1_2352 18 107 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 263
  (Polychromatic418967fa.accept_21_17_2_11_1_8656 17 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 107 263 (accept_3_2 16 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 107 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 107 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 107 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 263 (accept_3_2 13 107 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 263 (Polychromatic418967fa.accept_7_5_2_4_1_126
  12 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 263
  (Polychromatic418967fa.accept_22_11_19_21_1_11438 11 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 107 263 (accept_3_2 10 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 107 263 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 107 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 263 (Polychromatic418967fa.accept_22_8_19_21_1_16071 8 107
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 263 (accept_3_2 7 107 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6
  107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 263 (accept_3_2 4 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 107 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 263 (Polychromatic418967fa.accept_14_2_9_11_1_3054 2 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 263 (accept_3_2 1 107 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 107
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 263 (allA_of_3_0 106 106 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 263
  (allA_succ_of_accept 104 105 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 105 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 263 (accept_3_2 103 105 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 263
  (Polychromatic418967fa.accept_14_3_7_11_1_765 101 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 263 (accept_3_2 100 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 99 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 105 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 263 (accept_3_2 97 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 263 (Polychromatic418967fa.accept_13_5_1_3_1_878 96 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 95 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 263 (accept_3_2 94 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 263 (accept_3_2 91 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 89 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 263 (accept_3_2 88 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 263 (Polychromatic418967fa.accept_10_7_5_3_1_542 87 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 263 (accept_3_2 85 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 263
  (Polychromatic418967fa.accept_13_5_1_3_1_878 83 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 263 (accept_3_2 82 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 263 (Polychromatic418967fa.accept_17_13_3_8_1_6310 81 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 263 (accept_3_2 79 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 263 (accept_3_2 76 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 263 (accept_3_2 73 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 263 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 263 (accept_3_2 70 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 263 (Polychromatic418967fa.accept_13_4_1_3_1_3058 69 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 263 (accept_3_2 67 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 263
  (Polychromatic418967fa.accept_19_8_10_16_1_9418 65 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 105 263 (accept_3_2 64 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 105 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 105 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 263 (accept_3_2 61 105 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 263
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 60 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 105 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 105 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 263 (accept_3_2 58 105 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 56
  105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 263 (accept_3_2 55
  105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 105 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 263 (accept_3_2 52 105 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 105 263 (accept_3_2 49 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 105 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 105 263 (Polychromatic418967fa.accept_10_7_5_3_1_542 47 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 263 (accept_3_2 46 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 263 (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 105
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 263 (accept_3_2 43 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 105 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 105 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 263 (accept_3_2 40 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 263 (accept_3_2 37 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 263 (Polychromatic418967fa.accept_24_12_9_23_1_7477 36 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 263 (accept_3_2 34 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 263 (Polychromatic418967fa.accept_13_7_1_3_1_1523 33 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 263 (accept_3_2 31 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 263 (Polychromatic418967fa.accept_16_13_9_7_1_4532 29 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 263 (accept_3_2 28 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 263 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 105
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 263 (accept_3_2 25 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 263 (Polychromatic418967fa.accept_13_11_1_3_1_910 24 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 263 (accept_3_2 22 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 263 (accept_3_2 19 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 263 (accept_3_2 16 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 263 (accept_3_2 13 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 263 (Polychromatic418967fa.accept_13_11_1_3_1_910 11 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 263 (accept_3_2 10 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 263 (Polychromatic418967fa.accept_18_9_15_11_1_5693 9 105
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 263 (accept_3_2 7 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 263 (accept_3_2 4 105 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 105 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 263 (accept_3_2 1 105 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 263 (allA_succ_of_accept 103 104 263 (accept_3_2 103 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 104 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 102 104 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 104 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 101 104
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 104 263 (accept_3_2 100 104
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 104 263
  (Polychromatic418967fa.accept_6_3_2_5_1_32 99 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 104 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 98 104 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 104 263 (accept_3_2 97 104 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 104 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 104 263
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 95 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 104 263 (accept_3_2 94 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 104 263 (Polychromatic418967fa.accept_11_4_5_10_1_926 92 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 104 263 (accept_3_2 91 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 104 263 (Polychromatic418967fa.accept_19_14_9_16_1_7969 90 104
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 104 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 89 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 104 263 (accept_3_2 88 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 104 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 86 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 104 263 (accept_3_2 85 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 104 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 263
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 83 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 104 263 (accept_3_2 82 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 104 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 263 (accept_3_2 79 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 104 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 263
  (Polychromatic418967fa.accept_10_7_4_3_1_560 77 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 104 263 (accept_3_2 76 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 104 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 74 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 104 263 (accept_3_2 73 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 104 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 104 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 104 263 (accept_3_2 70 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 104 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 263 (accept_3_2 67 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 263 (accept_3_2 64 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 104 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 263 (accept_3_2 61 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 104 263 (accept_3_2 58 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 104 263 (Polychromatic418967fa.accept_18_2_14_11_1_3139 56 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 263 (accept_3_2 55 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 104 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 104 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 104 263 (accept_3_2 52 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 104 263 (Polychromatic418967fa.accept_11_6_5_10_1_2724 50 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 263 (accept_3_2 49 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 104 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 104 263 (accept_3_2 46 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 104 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 263 (accept_3_2 43 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 263
  (Polychromatic418967fa.accept_16_9_8_7_1_4529 41 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 104 263 (accept_3_2 40 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 104 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 263 (accept_3_2 37 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 263 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 263 (accept_3_2 34 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 263 (Polychromatic418967fa.accept_27_5_23_20_1_16070 32 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 263 (accept_3_2 31 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 104 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 263
  (Polychromatic418967fa.accept_10_9_4_3_1_539 29 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 263 (accept_3_2 28 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 263 (accept_3_2 25 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 263 (accept_3_2 22 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 263 (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 263 (accept_3_2 19 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 263 (Polychromatic418967fa.accept_19_18_9_16_1_6524 18 104
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 263 (accept_3_2 16 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 263 (accept_3_2 13 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 104 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 263
  (Polychromatic418967fa.accept_17_11_2_8_1_7569 11 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 263 (accept_3_2 10 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 263 (accept_3_2 7 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 104 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 263 (accept_3_2 4 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 263 (accept_3_2 1 104 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 263 (allA_of_3_0 103 103 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 263 (allA_succ_of_accept 101
  102 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 102 263 (accept_3_2 100 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 102 263 (Polychromatic418967fa.accept_13_8_11_3_1_3053 99 102 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 102 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 102 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 102 263 (accept_3_2 97 102 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 102 263 (Polychromatic418967fa.accept_9_6_3_2_1_431
  96 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 102 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 95 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 102 263 (accept_3_2 94 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 102 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 102 263 (Polychromatic418967fa.accept_13_1_11_3_1_901 92 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 263 (accept_3_2 91 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 102 263 (Polychromatic418967fa.accept_20_10_2_3_1_7425 90 102
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 102 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 102 263 (accept_3_2 88 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 102 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 102 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 86 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 102 263 (accept_3_2 85 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 102 263 (Polychromatic418967fa.accept_11_7_3_10_1_1461 84 102 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 102 263
  (Polychromatic418967fa.accept_13_5_11_3_1_902 83 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 102 263 (accept_3_2 82 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 102 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 102 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 263 (accept_3_2 79 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 102 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 102 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 102 263 (accept_3_2 76 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 102 263 (Polychromatic418967fa.accept_10_5_2_3_1_239 75 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 102 263 (Polychromatic418967fa.accept_19_17_7_16_1_9299 74 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 263 (accept_3_2 73 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 102 263 (Polychromatic418967fa.accept_13_7_11_3_1_1540 72 102
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 102 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 102 263 (accept_3_2 70 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 102 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 102 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 263 (accept_3_2 67 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 263 (Polychromatic418967fa.accept_13_1_11_3_1_901 66 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 102 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 102 263 (accept_3_2 64 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 102 263 (Polychromatic418967fa.accept_14_7_4_11_1_3038 63 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 102 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 263 (accept_3_2 61 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 102 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 102 263 (accept_3_2 58 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 102 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 102 263 (Polychromatic418967fa.accept_15_11_12_8_1_739 56 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 263 (accept_3_2 55 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 263 (Polychromatic418967fa.accept_13_2_11_3_1_873 54 102
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 102 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 102 263 (accept_3_2 52 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 102 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 102 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 263 (accept_3_2 49 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 263 (Polychromatic418967fa.accept_15_3_12_8_1_738 48 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 102 263
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 47 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 102 263 (accept_3_2 46 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 102 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 102 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 263 (accept_3_2 43 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 102 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 102 263 (accept_3_2 40 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 102 263 (Polychromatic418967fa.accept_20_19_2_3_1_4486 39 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 102 263 (Polychromatic418967fa.accept_20_18_2_3_1_3169 38 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 263 (accept_3_2 37 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 263 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 102
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 263 (accept_3_2 34 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 102 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 102 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 263 (accept_3_2 31 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 263 (Polychromatic418967fa.accept_20_10_2_3_1_7425 30 102 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 263 (accept_3_2 28 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 102 263 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 102 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 263 (accept_3_2 25 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 263 (accept_3_2 22 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 102 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 102 263 (Polychromatic418967fa.accept_13_7_11_3_1_1540 20 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 263 (accept_3_2 19 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 263 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 102
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 263 (accept_3_2 16 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 102 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 102 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 263 (accept_3_2 13 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 263 (Polychromatic418967fa.accept_19_12_7_16_1_10721 12 102 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 263
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 263 (accept_3_2 10 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 263 (accept_3_2 7 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 102 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 263 (accept_3_2 4 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 263 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 102 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 263 (Polychromatic418967fa.accept_13_2_11_3_1_873 2 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 263 (accept_3_2 1 102 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 102
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 263 (allA_succ_of_accept 100 101 263 (accept_3_2 100 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 99 101 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 101 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 263 (accept_3_2 97 101 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 263
  (Polychromatic418967fa.accept_22_8_13_21_1_16069 96 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 101 263 (Polychromatic418967fa.accept_15_5_11_8_1_1391 95 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 263 (accept_3_2 94 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 101 263 (Polychromatic418967fa.accept_13_2_10_3_1_1538 93 101
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 92 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 101 263 (accept_3_2 91 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 101 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 101 263 (Polychromatic418967fa.accept_11_1_2_10_1_1426 89 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 263 (accept_3_2 88 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 263 (Polychromatic418967fa.accept_15_12_11_8_1_1392 87 101
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 263 (accept_3_2 85 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 263 (Polychromatic418967fa.accept_13_6_10_3_1_897 84 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 101 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 263 (accept_3_2 82 101 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 263 (Polychromatic418967fa.accept_25_6_1_13_1_16068 81 101 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 263
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 80 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 263 (accept_3_2 79 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 263 (Polychromatic418967fa.accept_14_7_3_11_1_2199 77 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 263 (accept_3_2 76 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 263 (Polychromatic418967fa.accept_16_11_5_7_1_2395 75 101
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 101 263 (accept_3_2 73 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 101 263 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 101 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 263 (accept_3_2 70 101 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 263
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 68 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 263 (accept_3_2 67 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 263 (Polychromatic418967fa.accept_15_5_11_8_1_1391 65 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 263 (accept_3_2 64 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 263 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 101
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 263 (accept_3_2 61 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 263 (Polychromatic418967fa.accept_16_12_5_7_1_2360 60 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 263 (Polychromatic418967fa.accept_13_7_10_3_1_1505 59 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 263 (accept_3_2 58 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 101 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 263
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 263 (accept_3_2 55 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 263 (Polychromatic418967fa.accept_17_2_16_8_1_3881 53 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 263 (accept_3_2 52 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 263 (Polychromatic418967fa.accept_22_7_13_21_1_16067 51
  101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 263 (accept_3_2 49 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 263 (Polychromatic418967fa.accept_19_9_6_16_1_5116 47 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 263 (accept_3_2 46 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 263 (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 101
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 263
  (Polychromatic418967fa.accept_16_12_5_7_1_2360 44 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 263 (accept_3_2 43 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 101 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 263 (accept_3_2 40 101 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 263 (Polychromatic418967fa.accept_22_17_13_21_1_11455 39 101 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 263 (accept_3_2 37 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 263 (Polychromatic418967fa.accept_14_7_3_11_1_2199 35 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 263 (accept_3_2 34 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 263 (Polychromatic418967fa.accept_13_7_10_3_1_1505 33 101
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 263
  (Polychromatic418967fa.accept_10_2_1_3_1_233 32 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 263 (accept_3_2 31 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 101 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 263 (accept_3_2 28 101 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 263 (accept_3_2 25 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 263 (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 263 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 263 (accept_3_2 22 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 263 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 101
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 263 (accept_3_2 19 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 263 (Polychromatic418967fa.accept_22_17_13_21_1_11455 17 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 263 (accept_3_2 16 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 101 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 263 (accept_3_2 13 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 263 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 263 (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 263 (accept_3_2 10 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 263 (Polychromatic418967fa.accept_17_9_16_8_1_2721 9 101
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 263 (accept_3_2 7 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 263 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 263 (accept_3_2 4 101 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 263 (Polychromatic418967fa.accept_15_3_11_8_1_4186 3 101
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 263 (accept_3_2 1 101 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 263 (allA_of_3_0 100 100 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 263 (allA_succ_of_accept 98 99
  263 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 99 263 (accept_3_2 97 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96
  99 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 99 263 (Polychromatic418967fa.accept_16_15_3_7_1_3389 95 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 263 (accept_3_2 94 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 93 99
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 263 (accept_3_2 91 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 263 (Polychromatic418967fa.accept_16_10_3_7_1_8094 90 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 89 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 263 (accept_3_2 88 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 263 (accept_3_2 85 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 263 (Polychromatic418967fa.accept_13_5_8_3_1_1535 83 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 263 (accept_3_2 82 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 263 (accept_3_2 79 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 263 (Polychromatic418967fa.accept_15_3_9_8_1_3164 78 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 263 (Polychromatic418967fa.accept_15_2_9_8_1_736 77 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 263 (accept_3_2 76 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 263 (accept_3_2 73 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 263 (Polychromatic418967fa.accept_13_7_8_3_1_1533 72 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 263 (Polychromatic418967fa.accept_25_21_24_13_1_16066 71 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 263 (accept_3_2 70 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 99
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 263 (accept_3_2 67 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 263 (Polychromatic418967fa.accept_27_11_18_20_1_4390 65 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 263 (accept_3_2 64 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 263 (Polychromatic418967fa.accept_13_11_8_3_1_3016 63 99
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 263 (accept_3_2 61 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 263 (accept_3_2 58 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 263 (accept_3_2 55 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 263 (Polychromatic418967fa.accept_25_3_24_13_1_16065 53 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 263 (accept_3_2 52 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 263 (Polychromatic418967fa.accept_18_15_9_11_1_4371 51 99
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 263 (accept_3_2 49 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 263 (Polychromatic418967fa.accept_13_9_8_3_1_3045 48 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 263 (accept_3_2 46 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 263 (accept_3_2 43 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 263 (Polychromatic418967fa.accept_16_10_3_7_1_8094 42 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 263 (Polychromatic418967fa.accept_16_9_3_7_1_6883 41 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 263 (accept_3_2 40 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 263 (Polychromatic418967fa.accept_19_1_4_16_1_7997 39 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 263 (accept_3_2 37 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 263 (Polychromatic418967fa.accept_13_9_8_3_1_3045 35 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 263 (accept_3_2 34 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 263 (accept_3_2 31 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 263 (Polychromatic418967fa.accept_18_12_9_11_1_4370 30 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 263 (Polychromatic418967fa.accept_15_14_9_8_1_3165 29 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 263 (accept_3_2 28 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 263 (Polychromatic418967fa.accept_16_11_3_7_1_2375 27 99
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 263 (accept_3_2 25 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 263 (Polychromatic418967fa.accept_17_6_14_8_1_3858 23 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 263 (accept_3_2 22 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 99
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 263 (accept_3_2 19 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 263 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 263 (accept_3_2 16 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 263 (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 263 (accept_3_2 13 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 263 (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 263 (accept_3_2 10 99 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 99 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 263 (accept_3_2 7 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  263 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 99 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 99 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 263 (accept_3_2 4 99 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 99 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 99
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 263 (accept_3_2 1 99 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  263 (allA_succ_of_accept 97 98 263 (accept_3_2 97 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 96 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 263 (accept_3_2 94 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 92 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 263 (accept_3_2 91 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 263 (Polychromatic418967fa.accept_17_5_13_8_1_7556 90 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 263 (accept_3_2 88 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 86 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 263 (accept_3_2 85 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 263 (Polychromatic418967fa.accept_17_15_13_8_1_7603 83 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 263 (accept_3_2 82 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 98 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 263 (accept_3_2 79 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 263 (accept_3_2 76 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 263
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 74 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 263 (accept_3_2 73 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 263 (Polychromatic418967fa.accept_17_4_13_8_1_3874 72 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 263 (Polychromatic418967fa.accept_10_1_8_3_1_947 71 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 263 (accept_3_2 70 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 263 (accept_3_2 67 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 263 (accept_3_2 64 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 263
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 62 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 263 (accept_3_2 61 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 263 (accept_3_2 58 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 263
  (Polychromatic418967fa.accept_10_6_8_3_1_930 56 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 263 (accept_3_2 55 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 263 (Polychromatic418967fa.accept_17_3_13_8_1_11337 54 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 263 (accept_3_2 52 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 263 (accept_3_2 49 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 263 (Polychromatic418967fa.accept_13_8_7_3_1_430 47 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 263 (accept_3_2 46 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 263 (accept_3_2 43 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 263 (accept_3_2 40 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 263
  (Polychromatic418967fa.accept_17_4_13_8_1_3874 38 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 263 (accept_3_2 37 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 263 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 263 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 263 (accept_3_2 34 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 263 (accept_3_2 31 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 263 (accept_3_2 28 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 263
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 263 (accept_3_2 25 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 263 (accept_3_2 22 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 263 (accept_3_2 19 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 263 (Polychromatic418967fa.accept_19_18_3_16_1_7962 18 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 263 (accept_3_2 16 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 263 (accept_3_2 13 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 263 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 263 (accept_3_2 10 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 263 (accept_3_2 7 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  263 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 263 (accept_3_2 4 98 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 98 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 263 (Polychromatic418967fa.accept_19_2_3_16_1_6469
  2 98 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 263 (accept_3_2 1 98
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  263 (allA_of_3_0 97 97 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 263 (allA_succ_of_accept 95 96 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 95 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 96 263 (accept_3_2 94 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  96 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 96 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 92 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 263 (accept_3_2 91 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 96 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 96 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 89 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 263 (accept_3_2 88 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  96 263 (Polychromatic418967fa.accept_10_7_6_3_1_927 87 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 96 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 263 (accept_3_2 85 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 96 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 96 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 263 (accept_3_2 82 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  96 263 (Polychromatic418967fa.accept_19_5_1_16_1_6501 81 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 96 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 80 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 263 (accept_3_2 79 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 96 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 96 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 263 (accept_3_2 76 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  96 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 96 263 (Polychromatic418967fa.accept_13_9_5_3_1_428 74 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 263 (accept_3_2 73 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 96 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 263 (accept_3_2 70 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  96 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 96 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 263 (accept_3_2 67 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 263 (accept_3_2 64 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  96 263 (Polychromatic418967fa.accept_13_11_5_3_1_889 63 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 96 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 263 (accept_3_2 61 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 263 (Polychromatic418967fa.accept_13_8_5_3_1_427 60 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 96 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 263 (accept_3_2 58 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  96 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 96 263 (Polychromatic418967fa.accept_21_14_12_11_1_3956 56 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 263 (accept_3_2 55 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 263 (Polychromatic418967fa.accept_13_2_5_3_1_406 54 96 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 96 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 263 (accept_3_2 52 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  96 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 96 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 263 (accept_3_2 49 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 96 263
  (Polychromatic418967fa.accept_10_7_6_3_1_927 47 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 263 (accept_3_2 46 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  96 263 (Polychromatic418967fa.accept_13_6_5_3_1_426 45 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 96 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 263 (accept_3_2 43 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 263 (Polychromatic418967fa.accept_11_9_8_10_1_934 42 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 96 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 263 (accept_3_2 40 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  96 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 96 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 263 (accept_3_2 37 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 96 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 263 (accept_3_2 34 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  96 263 (Polychromatic418967fa.accept_18_15_6_11_1_5651 33 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 96 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 263 (accept_3_2 31 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 96 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 263 (accept_3_2 28 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  96 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 96 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 263 (accept_3_2 25 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 263 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 96 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 263 (accept_3_2 22 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 263 (accept_3_2 19 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 263 (accept_3_2 16 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 263 (accept_3_2 13 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 263
  (Polychromatic418967fa.accept_13_11_5_3_1_889 11 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 263 (accept_3_2 10 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  96 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 96 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 263 (accept_3_2 7 96 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 96 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 263 (accept_3_2 4 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 96 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 96 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 263 (accept_3_2 1 96 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 263
  (allA_succ_of_accept 94 95 263 (accept_3_2 94 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 93 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 263 (Polychromatic418967fa.accept_10_2_5_3_1_1408 92 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 263 (accept_3_2 91 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 263 (Polychromatic418967fa.accept_13_12_4_3_1_1528 90 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 89 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 263 (accept_3_2 88 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 87 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 263 (Polychromatic418967fa.accept_15_11_5_8_1_3157 86 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 263 (accept_3_2 85 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 95 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 263
  (Polychromatic418967fa.accept_16_3_15_7_1_3417 83 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 263 (accept_3_2 82 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 263 (Polychromatic418967fa.accept_25_6_20_13_1_16064 81 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 263 (accept_3_2 79 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 263
  (Polychromatic418967fa.accept_10_7_5_3_1_542 77 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 263 (accept_3_2 76 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 263 (Polychromatic418967fa.accept_15_14_5_8_1_3175 74 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 263 (accept_3_2 73 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 263 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 95 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 263 (accept_3_2 70 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 263 (Polychromatic418967fa.accept_10_8_5_3_1_543 68 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 263 (accept_3_2 67 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 263
  (Polychromatic418967fa.accept_20_5_15_3_1_4516 65 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 263 (accept_3_2 64 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 263 (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 263 (accept_3_2 61 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 263
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 59 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 263 (accept_3_2 58 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 263 (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 263 (accept_3_2 55 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 263 (Polychromatic418967fa.accept_16_6_15_7_1_1510 54 95
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 263 (accept_3_2 52 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 263 (Polychromatic418967fa.accept_18_14_5_11_1_5676 50 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 263 (accept_3_2 49 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 95 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 263
  (Polychromatic418967fa.accept_10_7_5_3_1_542 47 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 263 (accept_3_2 46 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 263 (Polychromatic418967fa.accept_20_5_15_3_1_4516 45 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 263 (accept_3_2 43 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 263
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 41 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 263 (accept_3_2 40 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 263 (Polychromatic418967fa.accept_10_8_5_3_1_543 38 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 263 (accept_3_2 37 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 263 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 263 (accept_3_2 34 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 263 (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 263 (accept_3_2 31 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 263
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 263 (accept_3_2 28 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 263 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 263 (accept_3_2 25 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 263
  (Polychromatic418967fa.accept_27_23_14_20_1_16063 23 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 95 263 (accept_3_2 22 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 95 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 95 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 263 (Polychromatic418967fa.accept_13_7_4_3_1_3064 20 95 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 263 (accept_3_2 19 95 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 263 (Polychromatic418967fa.accept_10_8_5_3_1_543
  18 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 263 (accept_3_2 16 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 263 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 263 (accept_3_2 13 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 263
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 263 (accept_3_2 10 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 263 (Polychromatic418967fa.accept_20_9_15_3_1_7470 9 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 263 (accept_3_2 7 95 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 95 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 263
  (Polychromatic418967fa.accept_20_5_15_3_1_4516 5 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 263 (accept_3_2 4 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  263 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 95 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 263 (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 95 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 263 (accept_3_2 1 95 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 263
  (allA_of_3_0 94 94 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 263 (allA_succ_of_accept 92 93 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 263 (accept_3_2 91 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 263 (accept_3_2 88 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 263 (accept_3_2 85 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 263 (Polychromatic418967fa.accept_15_9_3_8_1_3155 84 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 263 (accept_3_2 82 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 263 (Polychromatic418967fa.accept_11_4_5_10_1_926 81 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 263 (accept_3_2 79 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 263 (accept_3_2 76 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 263 (accept_3_2 73 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 263 (Polychromatic418967fa.accept_11_6_5_10_1_2724 72 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 263 (accept_3_2 70 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 263 (accept_3_2 67 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 263 (Polychromatic418967fa.accept_15_5_3_8_1_748 65 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 263 (accept_3_2 64 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 263 (accept_3_2 61 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 263 (accept_3_2 58 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 263 (Polychromatic418967fa.accept_13_5_2_3_1_1526 57 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 263 (accept_3_2 55 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 263 (accept_3_2 52 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 263 (accept_3_2 49 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 263 (accept_3_2 46 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 263 (Polychromatic418967fa.accept_19_7_17_16_1_6478 45 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 263 (accept_3_2 43 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 263 (accept_3_2 40 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 263 (Polychromatic418967fa.accept_11_6_5_10_1_2724 39 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 263 (accept_3_2 37 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 263 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 263 (accept_3_2 34 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 263 (accept_3_2 31 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 263 (Polychromatic418967fa.accept_24_5_21_23_1_9227 29 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 263 (accept_3_2 28 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 93 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 263 (accept_3_2 25 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 263 (accept_3_2 22 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 263 (Polychromatic418967fa.accept_19_2_17_16_1_6481 21 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 263 (accept_3_2 19 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 263 (accept_3_2 16 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 263 (accept_3_2 13 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 263 (Polychromatic418967fa.accept_13_11_2_3_1_883 11 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 263 (accept_3_2 10 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 263 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 93 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 263 (accept_3_2 7 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 93 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 263 (accept_3_2 4 93 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 93 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 263 (accept_3_2 1 93 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 263
  (allA_succ_of_accept 91 92 263 (accept_3_2 91 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 263 (Polychromatic418967fa.accept_20_10_12_3_1_6003 90 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 89 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 263 (accept_3_2 88 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 86 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 263 (accept_3_2 85 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 263 (Polychromatic418967fa.accept_13_6_1_3_1_1522 84 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 263 (accept_3_2 82 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 263 (accept_3_2 79 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 263 (Polychromatic418967fa.accept_25_3_17_13_1_16062 78 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 263 (Polychromatic418967fa.accept_21_14_8_11_1_10082 77 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 263 (accept_3_2 76 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 263 (accept_3_2 73 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 263 (Polychromatic418967fa.accept_13_7_1_3_1_1523 72 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 263 (Polychromatic418967fa.accept_10_1_2_3_1_1910 71 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 263 (accept_3_2 70 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 263 (accept_3_2 67 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 263 (Polychromatic418967fa.accept_10_5_2_3_1_239 65 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 263 (accept_3_2 64 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 263 (accept_3_2 61 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 263 (Polychromatic418967fa.accept_11_5_4_10_1_524 60 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 263 (accept_3_2 58 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 263
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 56 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 263 (accept_3_2 55 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 263 (Polychromatic418967fa.accept_16_5_12_7_1_3411 53 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 263 (accept_3_2 52 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 263 (accept_3_2 49 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 263 (Polychromatic418967fa.accept_17_14_7_8_1_7544 48 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 263 (accept_3_2 46 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 263
  (Polychromatic418967fa.accept_13_5_1_3_1_878 44 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 263 (accept_3_2 43 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 263 (Polychromatic418967fa.accept_22_20_4_21_1_8237 42 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 263 (Polychromatic418967fa.accept_10_1_2_3_1_1910 41 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 263 (accept_3_2 40 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 263 (accept_3_2 37 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 263 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 263 (accept_3_2 34 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 263
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 32 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 263 (accept_3_2 31 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 263 (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 263 (Polychromatic418967fa.accept_20_9_12_3_1_3191 29 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 263 (accept_3_2 28 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 263 (accept_3_2 25 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 263 (Polychromatic418967fa.accept_32_23_28_7_1_16061 23 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 263 (accept_3_2 22 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 263
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 263 (accept_3_2 19 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 263 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 263 (accept_3_2 16 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 263 (accept_3_2 13 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 263 (accept_3_2 10 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 263
  (Polychromatic418967fa.accept_16_8_12_7_1_2399 8 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 263 (accept_3_2 7 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  263 (Polychromatic418967fa.accept_13_6_1_3_1_1522 6 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 92 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 263 (accept_3_2 4 92 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 92 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 92 263 (accept_3_2 1 92 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 263
  (allA_of_3_0 91 91 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 263 (allA_succ_of_accept 89 90 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 90 263 (accept_3_2 88 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  90 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 90 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 86 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 90 263 (accept_3_2 85 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 90 263 (Polychromatic418967fa.accept_24_12_18_23_1_16060 84 90 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 90 263
  (Polychromatic418967fa.accept_16_3_10_7_1_4518 83 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 90 263 (accept_3_2 82 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  90 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 90 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 263 (accept_3_2 79 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 263 (Polychromatic418967fa.accept_11_1_2_10_1_1426 78 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 90 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 263 (accept_3_2 76 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  90 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 90 263 (Polychromatic418967fa.accept_13_9_12_3_1_907 74 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 263 (accept_3_2 73 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 90 263
  (Polychromatic418967fa.accept_17_3_5_8_1_1687 71 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 90 263 (accept_3_2 70 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  90 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 90 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 263 (accept_3_2 67 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 90 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 90 263 (accept_3_2 64 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  90 263 (Polychromatic418967fa.accept_17_12_5_8_1_7680 63 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 90 263 (Polychromatic418967fa.accept_16_14_10_7_1_2363 62 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 263 (accept_3_2 61 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 263 (Polychromatic418967fa.accept_19_3_14_16_1_10747 60 90
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 263 (accept_3_2 58 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  90 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 90 263 (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 263 (accept_3_2 55 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 90 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 263 (accept_3_2 52 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  90 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 90 263 (Polychromatic418967fa.accept_19_12_14_16_1_7935 50 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 263 (accept_3_2 49 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 263 (Polychromatic418967fa.accept_13_9_12_3_1_907 48 90 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 263 (accept_3_2 46 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  90 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 90 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 263 (accept_3_2 43 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 263 (Polychromatic418967fa.accept_20_2_10_3_1_9059 42 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 263 (accept_3_2 40 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  90 263 (Polychromatic418967fa.accept_20_19_10_3_1_13274 39 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 90 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 263 (accept_3_2 37 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 263 (Polychromatic418967fa.accept_19_17_14_16_1_3820 36 90 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 263
  (Polychromatic418967fa.accept_13_9_12_3_1_907 35 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 90 263 (accept_3_2 34 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  90 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 90 263 (Polychromatic418967fa.accept_19_13_14_16_1_6527 32 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 263 (accept_3_2 31 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 90 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 263 (accept_3_2 28 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  90 263 (Polychromatic418967fa.accept_20_7_10_3_1_949 27 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 90 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 263 (accept_3_2 25 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 263 (accept_3_2 22 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 90 263 (Polychromatic418967fa.accept_17_3_5_8_1_1687 20 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 263 (accept_3_2 19 90 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 263 (Polychromatic418967fa.accept_19_18_14_16_1_2601 18 90 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 263 (accept_3_2 16 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 263 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 263 (Polychromatic418967fa.accept_16_14_10_7_1_2363 14 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 263 (accept_3_2 13 90 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 90 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 263
  (Polychromatic418967fa.accept_19_11_14_16_1_9370 11 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 90 263 (accept_3_2 10 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 90 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 263 (Polychromatic418967fa.accept_22_8_2_21_1_9874 8 90 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 263 (accept_3_2 7 90 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 263 (Polychromatic418967fa.accept_24_6_18_23_1_9275
  6 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 263 (accept_3_2 4 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90
  263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 90 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 90 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 263 (accept_3_2 1 90 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 90 263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 89 263 (allA_succ_of_accept 88 89 263 (accept_3_2 88 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 87 89 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 89 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 263 (accept_3_2 85 89 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 84
  89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 263 (accept_3_2 82 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 263 (Polychromatic418967fa.accept_15_6_14_8_1_245 81 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 263 (Polychromatic418967fa.accept_13_2_11_3_1_873 80 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 263 (accept_3_2 79 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 89 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 77 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 263 (accept_3_2 76 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 263 (accept_3_2 73 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 89 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 263 (accept_3_2 70 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 263 (accept_3_2 67 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 89 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 263 (accept_3_2 64 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 263 (Polychromatic418967fa.accept_17_12_4_8_1_5073 63 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 263 (accept_3_2 61 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 89 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 263 (accept_3_2 58 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 263 (Polychromatic418967fa.accept_10_6_9_3_1_935 56 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 263 (accept_3_2 55 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 263
  (Polychromatic418967fa.accept_11_9_1_10_1_920 53 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 263 (accept_3_2 52 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 263 (accept_3_2 49 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 89 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 263
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 47 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 263 (accept_3_2 46 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 263 (Polychromatic418967fa.accept_16_13_9_7_1_4532 45 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 263 (accept_3_2 43 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 263 (accept_3_2 40 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 263 (accept_3_2 37 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 89 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 263
  (Polychromatic418967fa.accept_11_2_1_10_1_196 35 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 263 (accept_3_2 34 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 263 (accept_3_2 31 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 263 (accept_3_2 28 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 263 (accept_3_2 25 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 89 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 263 (accept_3_2 22 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 263 (accept_3_2 19 89 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 263
  (Polychromatic418967fa.accept_19_17_13_16_1_5118 17 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 89 263 (accept_3_2 16 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 89 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 89 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 263 (accept_3_2 13 89 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 12
  89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 263
  (Polychromatic418967fa.accept_19_11_13_16_1_8002 11 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 89 263 (accept_3_2 10 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 89 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 89 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 89 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 263 (accept_3_2 7 89 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 263 (accept_3_2 4 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  263 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 89 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 263 (accept_3_2 1 89 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 263 (allA_of_3_0 88 88 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 263
  (allA_succ_of_accept 86 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 263 (accept_3_2 85 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 83
  87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 263 (accept_3_2 82 87
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 263
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 263 (accept_3_2 79 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 77
  87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 263 (accept_3_2 76 87
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 263
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 263 (accept_3_2 73 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 263 (Polychromatic418967fa.accept_13_7_9_3_1_1504 72 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 71
  87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 263 (accept_3_2 70 87
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 263 (accept_3_2 67 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 263 (Polychromatic418967fa.accept_10_5_7_3_1_561
  65 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 263 (accept_3_2 64
  87 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 263
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 63 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 263 (accept_3_2 61 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 263 (Polychromatic418967fa.accept_13_8_9_3_1_2213 60 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 59
  87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 263 (accept_3_2 58 87
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 263 (accept_3_2 55 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 263 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 53
  87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 263 (accept_3_2 52 87
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 263
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 51 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 263 (accept_3_2 49 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 263 (Polychromatic418967fa.accept_13_8_9_3_1_2213
  47 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 263 (accept_3_2 46
  87 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 263 (accept_3_2 43 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 263 (Polychromatic418967fa.accept_18_6_15_11_1_3141 42 87 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 263 (accept_3_2 40 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 263 (accept_3_2 37 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 87 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 263 (accept_3_2 34 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 263 (accept_3_2 31 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 87 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 263 (accept_3_2 28 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 263 (accept_3_2 25 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 263 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 87 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 263 (accept_3_2 22 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 263 (accept_3_2 19 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 263 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 87 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 263 (accept_3_2 16 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 263 (accept_3_2 13 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 87 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 263
  (Polychromatic418967fa.accept_15_11_12_8_1_739 11 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 263 (accept_3_2 10 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 263 (accept_3_2 7 87 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 87 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 263 (accept_3_2 4 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 263 (accept_3_2 1 87 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 86 263 (allA_succ_of_accept 85 86 263 (accept_3_2 85 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 86 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 86 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 86 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 86 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 263 (accept_3_2 82 86 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 81
  86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 80 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 263 (accept_3_2 79 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 263 (accept_3_2 76 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 263
  (Polychromatic418967fa.accept_11_8_9_10_1_503 74 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 263 (accept_3_2 73 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 263 (Polychromatic418967fa.accept_13_7_8_3_1_1533 72 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 263 (accept_3_2 70 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 263 (accept_3_2 67 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 263 (accept_3_2 64 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 263
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 263 (accept_3_2 61 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 263 (Polychromatic418967fa.accept_10_9_6_3_1_545 59 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 263 (accept_3_2 58 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 263
  (Polychromatic418967fa.accept_11_1_9_10_1_184 56 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 263 (accept_3_2 55 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 263 (accept_3_2 52 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 263
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 50 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 263 (accept_3_2 49 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 263 (accept_3_2 46 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 263 (accept_3_2 43 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 263 (accept_3_2 40 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 263
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 263 (accept_3_2 37 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 263 (Polychromatic418967fa.accept_31_5_24_15_1_16059 36 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 263 (accept_3_2 34 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 263 (accept_3_2 31 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 263 (accept_3_2 28 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 263 (accept_3_2 25 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 263 (accept_3_2 22 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 263
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 263 (accept_3_2 19 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 263 (accept_3_2 16 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 263
  (Polychromatic418967fa.accept_21_14_2_11_1_8625 14 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 263 (accept_3_2 13 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 263 (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 263 (accept_3_2 10 86 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 263 (accept_3_2 7 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 263 (accept_3_2 4 86 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 263 (Polychromatic418967fa.accept_18_2_14_11_1_3139
  2 86 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 263 (accept_3_2 1 86
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 263
  (allA_of_3_0 85 85 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 263 (allA_succ_of_accept 83 84 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 83 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 263 (accept_3_2 82 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 263 (Polychromatic418967fa.accept_18_9_12_11_1_5642 81 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 263 (accept_3_2 79 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 77 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 263 (accept_3_2 76 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 263 (Polychromatic418967fa.accept_13_9_6_3_1_1514 74 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 263 (accept_3_2 73 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 263 (Polychromatic418967fa.accept_16_8_4_7_1_3390 72 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 263 (accept_3_2 70 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 263 (accept_3_2 67 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 263 (Polychromatic418967fa.accept_13_1_6_3_1_1547 66 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 263
  (Polychromatic418967fa.accept_17_14_16_8_1_3861 65 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 263 (accept_3_2 64 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 263 (Polychromatic418967fa.accept_15_3_9_8_1_3164 63 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 263 (accept_3_2 61 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 263 (accept_3_2 58 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 263 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 263 (Polychromatic418967fa.accept_16_8_4_7_1_3390 56 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 263 (accept_3_2 55 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 263 (Polychromatic418967fa.accept_20_14_4_3_1_2006 54 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 263 (accept_3_2 52 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 263 (accept_3_2 49 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 263 (Polychromatic418967fa.accept_13_9_6_3_1_1514 48 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 263
  (Polychromatic418967fa.accept_10_7_4_3_1_560 47 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 263 (accept_3_2 46 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 263 (Polychromatic418967fa.accept_16_13_4_7_1_1537 45 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 263 (accept_3_2 43 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 263 (accept_3_2 40 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 263 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 263 (Polychromatic418967fa.accept_27_11_3_20_1_16058 38 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 263 (accept_3_2 37 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 263 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 84 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 263 (accept_3_2 34 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 263 (accept_3_2 31 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 263 (Polychromatic418967fa.accept_16_14_4_7_1_2380 30 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 263
  (Polychromatic418967fa.accept_10_9_4_3_1_539 29 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 263 (accept_3_2 28 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 263 (accept_3_2 25 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 263 (accept_3_2 22 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 263 (Polychromatic418967fa.accept_20_1_4_3_1_9085 21 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 263 (Polychromatic418967fa.accept_19_1_8_16_1_6488 20 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 263 (accept_3_2 19 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 263 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 84 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 263 (accept_3_2 16 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 263 (accept_3_2 13 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 263 (Polychromatic418967fa.accept_16_12_4_7_1_3391 12 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 263 (accept_3_2 10 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 263 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 263 (accept_3_2 7 84 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 84 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 263 (accept_3_2 4 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  263 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 84 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 84 263 (Polychromatic418967fa.accept_15_2_9_8_1_736 2 84 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 263 (accept_3_2 1 84 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 83 263 (allA_succ_of_accept 82 83 263 (accept_3_2 82 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 83 263 (Polychromatic418967fa.accept_17_13_15_8_1_3860 81 83 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 83 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 263 (accept_3_2 79 83 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 263
  (Polychromatic418967fa.accept_17_10_15_8_1_6324 78 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 83 263 (Polychromatic418967fa.accept_21_14_20_11_1_8630 77 83 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 83 263 (accept_3_2 76 83 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 83 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 83 263 (Polychromatic418967fa.accept_13_9_5_3_1_428
  74 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 263 (accept_3_2 73
  83 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 83 263 (Polychromatic418967fa.accept_11_5_6_10_1_1432 71 83 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 83 263 (accept_3_2 70 83 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 83 263 (Polychromatic418967fa.accept_19_12_7_16_1_10721 69 83 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 83 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 83 263 (accept_3_2 67 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  83 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 83 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 83 263 (accept_3_2 64 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 83 263 (Polychromatic418967fa.accept_13_11_5_3_1_889 63 83 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 83 263
  (Polychromatic418967fa.accept_22_18_17_21_1_14485 62 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 83 263 (accept_3_2 61 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 83 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 83 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 83 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 83 263 (accept_3_2 58 83 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 83 263 (Polychromatic418967fa.accept_16_9_3_7_1_6883
  57 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 83 263
  (Polychromatic418967fa.accept_21_14_20_11_1_8630 56 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 83 263 (accept_3_2 55 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 83 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 83 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 263 (Polychromatic418967fa.accept_13_1_5_3_1_888 53 83 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 83 263 (accept_3_2 52 83 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 83 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 51
  83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 83 263
  (Polychromatic418967fa.accept_13_11_5_3_1_889 50 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 83 263 (accept_3_2 49 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  83 263 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 83 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 83 263 (accept_3_2 46 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 83 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 83 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 83 263 (accept_3_2 43 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  83 263 (Polychromatic418967fa.accept_16_10_3_7_1_8094 42 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 83 263 (Polychromatic418967fa.accept_13_2_5_3_1_406 41 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 83 263 (accept_3_2 40 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 83 263 (Polychromatic418967fa.accept_21_18_20_11_1_3927 39 83 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 83 263 (accept_3_2 37 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  83 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 83 263 (Polychromatic418967fa.accept_13_9_5_3_1_428 35 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 263 (accept_3_2 34 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 83 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 263
  (Polychromatic418967fa.accept_13_6_5_3_1_426 32 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 263 (accept_3_2 31 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 263 (Polychromatic418967fa.accept_19_10_7_16_1_9311 29 83 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 263 (accept_3_2 28 83 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 263 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 83
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 263 (accept_3_2 25 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 263 (accept_3_2 22 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 263 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 83 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 263
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 263 (accept_3_2 19 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 263 (Polychromatic418967fa.accept_21_18_20_11_1_3927 18 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 263 (accept_3_2 16 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 263 (Polychromatic418967fa.accept_13_2_5_3_1_406 15 83 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 263
  (Polychromatic418967fa.accept_13_1_5_3_1_888 14 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 263 (accept_3_2 13 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 263 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 263 (accept_3_2 10 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 83 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 263
  (Polychromatic418967fa.accept_13_8_5_3_1_427 8 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 263 (accept_3_2 7 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  263 (Polychromatic418967fa.accept_13_6_5_3_1_426 6 83 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 83 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 263 (accept_3_2 4 83 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 83 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 83 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 83
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 263 (accept_3_2 1 83 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 263 (allA_of_3_0
  82 82 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 263 (allA_succ_of_accept 80 81 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 81 263 (accept_3_2 79 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  81 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 81 263 (Polychromatic418967fa.accept_15_2_6_8_1_754 77 81 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 263 (accept_3_2 76 81 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 81 263 (accept_3_2 73 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  81 263 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 81 263 (Polychromatic418967fa.accept_11_5_4_10_1_524 71 81 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 263 (accept_3_2 70 81 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 263 (Polychromatic418967fa.accept_18_15_9_11_1_4371 69 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 263 (accept_3_2 67 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  81 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 81 263 (Polychromatic418967fa.accept_19_8_5_16_1_2589 65 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 263 (accept_3_2 64 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 81 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 81 263 (accept_3_2 61 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  81 263 (Polychromatic418967fa.accept_11_5_4_10_1_524 60 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 81 263 (Polychromatic418967fa.accept_15_14_6_8_1_1410 59 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 263 (accept_3_2 58 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 263 (Polychromatic418967fa.accept_25_7_6_13_1_16057 57 81
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 263 (accept_3_2 55 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 263 (Polychromatic418967fa.accept_20_13_1_3_1_11831 53 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 263 (accept_3_2 52 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 81 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 263 (accept_3_2 49 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 263 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 263 (Polychromatic418967fa.accept_15_2_6_8_1_754 47 81 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 263 (accept_3_2 46 81 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 263 (Polychromatic418967fa.accept_20_5_1_3_1_5983 45 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 263 (accept_3_2 43 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 263 (Polychromatic418967fa.accept_19_3_5_16_1_13380 41 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 263 (accept_3_2 40 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 81 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 263 (accept_3_2 37 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 263 (Polychromatic418967fa.accept_22_14_15_21_1_4974 36 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 263 (Polychromatic418967fa.accept_21_14_18_11_1_3961 35 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 263 (accept_3_2 34 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 263 (Polychromatic418967fa.accept_18_15_9_11_1_4371 33 81
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 263 (accept_3_2 31 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 263 (Polychromatic418967fa.accept_15_14_6_8_1_1410 29 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 263 (accept_3_2 28 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 263 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 81 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 263 (accept_3_2 25 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 263 (Polychromatic418967fa.accept_16_8_1_7_1_2355 24 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 263 (Polychromatic418967fa.accept_28_23_25_11_1_16056 23 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 263 (accept_3_2 22 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 263 (Polychromatic418967fa.accept_17_4_13_8_1_3874 21 81
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 263 (accept_3_2 19 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 263 (Polychromatic418967fa.accept_15_2_6_8_1_754 17 81 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 263 (accept_3_2 16 81 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 263 (accept_3_2 13 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 263 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 263 (Polychromatic418967fa.accept_19_11_5_16_1_1456 11 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 263 (accept_3_2 10 81 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 263 (Polychromatic418967fa.accept_21_9_18_11_1_8644 9 81 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 263 (accept_3_2 7 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 263 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 81 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 263 (accept_3_2 4 81 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 81 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 263 (accept_3_2 1 81 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 263
  (allA_succ_of_accept 79 80 263 (accept_3_2 79 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 263 (accept_3_2 76 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 263 (accept_3_2 73 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 263 (Polychromatic418967fa.accept_15_12_5_8_1_5247 72 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 263 (accept_3_2 70 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 263 (accept_3_2 67 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 263 (Polychromatic418967fa.accept_21_2_17_11_1_7037 65 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 263 (accept_3_2 64 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 263 (accept_3_2 61 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 263 (accept_3_2 58 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 263
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 263 (accept_3_2 55 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 263 (Polychromatic418967fa.accept_17_3_12_8_1_1688 54 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 263 (Polychromatic418967fa.accept_13_1_2_3_1_911 53 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 263 (accept_3_2 52 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 263 (accept_3_2 49 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 263 (Polychromatic418967fa.accept_19_9_4_16_1_2586 47 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 263 (accept_3_2 46 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 263
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 44 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 263 (accept_3_2 43 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 263 (accept_3_2 40 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 263 (accept_3_2 37 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 263 (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 263 (accept_3_2 34 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 263 (accept_3_2 31 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 263 (accept_3_2 28 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 263 (accept_3_2 25 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 263 (accept_3_2 22 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 263 (accept_3_2 19 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 263 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 263 (Polychromatic418967fa.accept_23_17_11_10_1_11257 17 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 263 (accept_3_2 16 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 263 (accept_3_2 13 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 263 (Polychromatic418967fa.accept_13_11_2_3_1_883 11 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 263 (accept_3_2 10 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 263 (accept_3_2 7 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 80 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 263 (accept_3_2 4 80 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  80 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 263 (accept_3_2 1 80 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 263 (allA_of_3_0 79
  79 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 263 (allA_succ_of_accept 77 78 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 263 (accept_3_2 76 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 263 (Polychromatic418967fa.accept_14_4_8_11_1_794 74 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 263 (accept_3_2 73 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 263 (Polychromatic418967fa.accept_15_12_3_8_1_5245 72 78 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 263 (accept_3_2 70 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 263 (accept_3_2 67 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 78 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 263 (accept_3_2 64 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 263 (Polychromatic418967fa.accept_16_15_14_7_1_10555 63 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 263 (accept_3_2 61 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 263 (Polychromatic418967fa.accept_14_4_8_11_1_794 60 78 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 263 (accept_3_2 58 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 263 (Polychromatic418967fa.accept_10_6_8_3_1_930 56 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 263 (accept_3_2 55 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 78 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 263 (accept_3_2 52 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 263 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 263 (accept_3_2 49 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 78 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 263 (accept_3_2 46 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 263 (accept_3_2 43 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 263 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 78 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 263 (accept_3_2 40 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 263 (accept_3_2 37 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 263 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 78 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 263 (accept_3_2 34 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 263 (accept_3_2 31 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 78 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 263 (accept_3_2 28 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 263 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 263 (accept_3_2 25 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 78 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 263 (accept_3_2 22 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 263 (Polychromatic418967fa.accept_11_9_1_10_1_920 20 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 263 (accept_3_2 19 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 263 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 78 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 263 (accept_3_2 16 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 263 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 263 (accept_3_2 13 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 78 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 263
  (Polychromatic418967fa.accept_10_1_8_3_1_947 11 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 263 (accept_3_2 10 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 78 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 263 (accept_3_2 7 78 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 78 263 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 78 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 263 (accept_3_2 4 78 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 263
  (Polychromatic418967fa.accept_11_2_1_10_1_196 2 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 263 (accept_3_2 1 78 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 263
  (allA_succ_of_accept 76 77 263 (accept_3_2 76 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 263 (accept_3_2 73 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 263 (Polychromatic418967fa.accept_19_15_1_16_1_6499 72 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 263 (accept_3_2 70 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 263 (Polychromatic418967fa.accept_16_4_13_7_1_4522 68 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 263 (accept_3_2 67 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 77 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 65 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 263 (accept_3_2 64 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 263 (Polychromatic418967fa.accept_22_19_11_21_1_11454 63 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 263 (accept_3_2 61 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 263
  (Polychromatic418967fa.accept_14_3_7_11_1_765 59 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 263 (accept_3_2 58 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 263 (Polychromatic418967fa.accept_10_6_7_3_1_547 56 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 263 (accept_3_2 55 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 263 (accept_3_2 52 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 263 (accept_3_2 49 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 263
  (Polychromatic418967fa.accept_21_5_14_11_1_10102 47 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 77 263 (accept_3_2 46 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 77 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 77 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 77 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 263 (accept_3_2 43 77 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 263
  (Polychromatic418967fa.accept_13_2_12_3_1_415 41 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 263 (accept_3_2 40 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 263 (accept_3_2 37 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 263 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 263 (accept_3_2 34 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 263 (Polychromatic418967fa.accept_14_4_7_11_1_790 32 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 263 (accept_3_2 31 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 263
  (Polychromatic418967fa.accept_19_10_1_16_1_7977 29 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 263 (accept_3_2 28 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 263 (Polychromatic418967fa.accept_19_8_1_16_1_13429 27 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 263 (accept_3_2 25 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 263
  (Polychromatic418967fa.accept_17_6_9_8_1_6316 23 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 263 (accept_3_2 22 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 263 (Polychromatic418967fa.accept_16_4_13_7_1_4522 20 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 263 (accept_3_2 19 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 263 (accept_3_2 16 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 263 (accept_3_2 13 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 263
  (Polychromatic418967fa.accept_17_11_9_8_1_5038 11 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 263 (accept_3_2 10 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 263 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 263 (accept_3_2 7 77 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 263 (accept_3_2 4 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  263 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 77 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 263 (accept_3_2 1 77 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 263 (allA_of_3_0 76 76 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 263 (allA_succ_of_accept 74 75
  263 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 263 (accept_3_2 73 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 263 (accept_3_2 70 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 75 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 263 (accept_3_2 67 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 263 (Polychromatic418967fa.accept_16_2_11_7_1_2352 66 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 263 (accept_3_2 64 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 263 (Polychromatic418967fa.accept_11_8_9_10_1_503 63 75 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 263 (accept_3_2 61 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 263 (accept_3_2 58 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 75 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 263 (accept_3_2 55 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 263 (Polychromatic418967fa.accept_13_2_10_3_1_1538 54 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 263 (accept_3_2 52 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 75 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 263 (accept_3_2 49 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 263 (Polychromatic418967fa.accept_10_7_5_3_1_542 47 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 263 (accept_3_2 46 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 45 75 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 263 (accept_3_2 43 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 263 (accept_3_2 40 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 263 (Polychromatic418967fa.accept_21_18_12_11_1_7078 39 75 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 263 (accept_3_2 37 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 263 (accept_3_2 34 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 75 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 263 (accept_3_2 31 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 263 (accept_3_2 28 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 263 (accept_3_2 25 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 263 (accept_3_2 22 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 75 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 263 (accept_3_2 19 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 263 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 263 (accept_3_2 16 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 75 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 263 (accept_3_2 13 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 263 (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 75 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 263 (accept_3_2 10 75 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 263 (accept_3_2 7 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  263 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 75 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 263 (accept_3_2 4 75 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 263 (Polychromatic418967fa.accept_16_3_11_7_1_770 3 75 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 263 (accept_3_2 1 75 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 263 (allA_succ_of_accept
  73 74 263 (accept_3_2 73 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 263
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 72 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 263 (Polychromatic418967fa.accept_13_6_9_3_1_915 71 74 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 263 (accept_3_2 70 74 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 263 (Polychromatic418967fa.accept_12_8_2_11_1_246
  68 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 263 (accept_3_2 67
  74 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 263
  (Polychromatic418967fa.accept_15_6_14_8_1_245 66 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 263 (accept_3_2 64 74 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 263
  (Polychromatic418967fa.accept_16_14_10_7_1_2363 62 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 263 (accept_3_2 61 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 263 (Polychromatic418967fa.accept_13_8_9_3_1_2213 60 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 263 (Polychromatic418967fa.accept_10_9_4_3_1_539 59 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 263 (accept_3_2 58 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 263 (accept_3_2 55 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 263 (Polychromatic418967fa.accept_13_2_9_3_1_2212 54 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 263 (accept_3_2 52 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 74 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 263
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 50 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 263 (accept_3_2 49 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 263 (Polychromatic418967fa.accept_17_14_6_8_1_7688 48 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 263 (Polychromatic418967fa.accept_10_7_4_3_1_560 47 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 263 (accept_3_2 46 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 263 (accept_3_2 43 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 263 (Polychromatic418967fa.accept_11_9_8_10_1_934 42 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 263 (accept_3_2 40 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 74 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 263
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 38 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 263 (accept_3_2 37 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 263 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 263 (Polychromatic418967fa.accept_14_7_4_11_1_3038 35 74 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 263 (accept_3_2 34 74 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 263 (accept_3_2 31 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 263 (Polychromatic418967fa.accept_16_14_10_7_1_2363 30 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 263 (accept_3_2 28 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 74 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 263
  (Polychromatic418967fa.accept_17_9_6_8_1_6315 26 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 263 (accept_3_2 25 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 263 (Polychromatic418967fa.accept_15_9_14_8_1_1396 24 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 263 (Polychromatic418967fa.accept_22_1_8_21_1_16055 23 74 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 263 (accept_3_2 22 74 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 263
  (Polychromatic418967fa.accept_11_9_8_10_1_934 20 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 263 (accept_3_2 19 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 263 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 263 (accept_3_2 16 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 74 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 263
  (Polychromatic418967fa.accept_16_14_10_7_1_2363 14 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 263 (accept_3_2 13 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 263 (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 263 (Polychromatic418967fa.accept_20_11_14_3_1_5975 11 74 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 263 (accept_3_2 10 74 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 263 (accept_3_2 7 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  263 (Polychromatic418967fa.accept_13_6_9_3_1_915 6 74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 263 (accept_3_2 4 74 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 263 (Polychromatic418967fa.accept_13_2_9_3_1_2212 2
  74 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 263 (accept_3_2 1 74 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 263 (allA_of_3_0 73 73 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 263 (allA_succ_of_accept 71 72 263
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 71 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 263 (accept_3_2 70 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 68 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 263 (accept_3_2 67 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 263 (Polychromatic418967fa.accept_13_1_7_3_1_1503 66 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 263
  (Polychromatic418967fa.accept_10_5_2_3_1_239 65 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 263 (accept_3_2 64 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 263 (Polychromatic418967fa.accept_13_11_7_3_1_894 63 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 263 (accept_3_2 61 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 263 (Polychromatic418967fa.accept_11_5_6_10_1_1432 60 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 263
  (Polychromatic418967fa.accept_22_15_6_21_1_16054 59 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 72 263 (accept_3_2 58 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 72 263 (Polychromatic418967fa.accept_16_9_8_7_1_4529 57 72 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 263 (Polychromatic418967fa.accept_13_4_7_3_1_92 56 72 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 263 (accept_3_2 55 72 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 54
  72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 263
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 53 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 263 (accept_3_2 52 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 263 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 263 (Polychromatic418967fa.accept_13_11_7_3_1_894 50 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 263 (accept_3_2 49 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 263 (accept_3_2 46 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 263 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 263 (Polychromatic418967fa.accept_16_12_8_7_1_4530 44 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 263 (accept_3_2 43 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 263 (Polychromatic418967fa.accept_23_19_3_10_1_16053 42 72
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 263
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 263 (accept_3_2 40 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 263 (Polychromatic418967fa.accept_19_1_15_16_1_2553 39 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 263 (Polychromatic418967fa.accept_11_5_6_10_1_1432 38 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 263 (accept_3_2 37 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 263 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 72
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 263
  (Polychromatic418967fa.accept_10_5_2_3_1_239 35 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 263 (accept_3_2 34 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 263 (Polychromatic418967fa.accept_19_13_15_16_1_13410 32 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 263 (accept_3_2 31 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 263 (Polychromatic418967fa.accept_13_4_7_3_1_92 30 72 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 263
  (Polychromatic418967fa.accept_17_12_4_8_1_5073 29 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 263 (accept_3_2 28 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 263 (accept_3_2 25 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 263 (Polychromatic418967fa.accept_13_11_7_3_1_894 24 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 263
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 263 (accept_3_2 22 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 263 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 263 (accept_3_2 19 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 263 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 263
  (Polychromatic418967fa.accept_13_4_7_3_1_92 17 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 263 (accept_3_2 16 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 263 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 263 (Polychromatic418967fa.accept_13_1_7_3_1_1503 14 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 263 (accept_3_2 13 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 263
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 263 (accept_3_2 10 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 263 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 263 (Polychromatic418967fa.accept_13_8_7_3_1_430 8 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 263 (accept_3_2 7 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 72 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 263 (accept_3_2 4 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  263 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 72 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 72 263 (Polychromatic418967fa.accept_21_2_9_11_1_13096 2 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 263 (accept_3_2 1 72 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 263 (allA_succ_of_accept 70 71 263 (accept_3_2 70 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 71 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 71 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 263 (accept_3_2 67 71 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 66
  71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 263
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 65 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 263 (accept_3_2 64 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 263 (Polychromatic418967fa.accept_15_3_11_8_1_4186 63 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 263 (Polychromatic418967fa.accept_10_2_1_3_1_233 62 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 263 (accept_3_2 61 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 71 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 263 (accept_3_2 58 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 263 (Polychromatic418967fa.accept_17_5_3_8_1_1697 56 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 263 (accept_3_2 55 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 71 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 263
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 53 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 263 (accept_3_2 52 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 263 (accept_3_2 49 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 71 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 263 (accept_3_2 46 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 263 (Polychromatic418967fa.accept_13_5_6_3_1_868 44 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 263 (accept_3_2 43 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 71 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 263 (accept_3_2 40 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 263 (accept_3_2 37 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 263 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 71 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 263
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 263 (accept_3_2 34 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 263 (accept_3_2 31 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 71 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 263
  (Polychromatic418967fa.accept_17_12_3_8_1_7627 29 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 263 (accept_3_2 28 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 263 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 263 (accept_3_2 25 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 263 (accept_3_2 22 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 263 (Polychromatic418967fa.accept_15_5_11_8_1_1391 20 71 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 263 (accept_3_2 19 71 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 263 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 71 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 263 (accept_3_2 16 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 263 (accept_3_2 13 71 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 263
  (Polychromatic418967fa.accept_19_11_14_16_1_9370 11 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 71 263 (accept_3_2 10 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 71 263 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 71 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 263 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 71 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 263 (accept_3_2 7 71 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 6
  71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 263 (accept_3_2 4 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 71 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 263 (Polychromatic418967fa.accept_10_2_1_3_1_233 2 71 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 263 (accept_3_2 1 71 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 263
  (allA_of_3_0 70 70 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 263 (allA_succ_of_accept 68 69 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 263 (accept_3_2 67 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 263 (accept_3_2 64 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 69 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 263 (accept_3_2 61 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 263 (Polychromatic418967fa.accept_16_12_5_7_1_2360 60 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 263 (accept_3_2 58 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 69 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 263 (accept_3_2 55 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 263 (accept_3_2 52 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 69 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 263 (accept_3_2 49 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 263 (accept_3_2 46 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 263 (accept_3_2 43 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 263 (accept_3_2 40 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 69 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 263 (accept_3_2 37 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 263 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 263 (accept_3_2 34 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 263 (accept_3_2 31 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 263 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 69 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 263 (accept_3_2 28 69 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 69 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 263 (accept_3_2 25 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 263 (accept_3_2 22 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 263 (accept_3_2 19 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 263 (accept_3_2 16 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 69 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 263 (accept_3_2 13 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 263 (Polychromatic418967fa.accept_16_11_5_7_1_2395 11 69 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 263 (accept_3_2 10 69 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 263 (accept_3_2 7 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 69 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 263 (accept_3_2 4 69 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 263 (accept_3_2 1 69 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 263 (allA_succ_of_accept 67 68
  263 (accept_3_2 67 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 263
  (Polychromatic418967fa.accept_9_3_5_2_1_28 66 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 263 (accept_3_2 64 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 62
  68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 263 (accept_3_2 61 68
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 263
  (Polychromatic418967fa.accept_9_6_5_2_1_421 60 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 263 (accept_3_2 58 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 263 (Polychromatic418967fa.accept_10_6_8_3_1_930
  56 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 263 (accept_3_2 55
  68 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 263
  (Polychromatic418967fa.accept_20_14_8_3_1_6011 54 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 263 (accept_3_2 52 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 50
  68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 263 (accept_3_2 49 68
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 68 263 (Polychromatic418967fa.accept_22_3_2_21_1_16052 47 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 263 (accept_3_2 46 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 68 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 44
  68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 263 (accept_3_2 43 68
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 263
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 263 (accept_3_2 40 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 263 (Polychromatic418967fa.accept_12_2_8_11_1_31
  38 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 263 (accept_3_2 37
  68 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 263 (accept_3_2 34 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 263
  (Polychromatic418967fa.accept_19_13_11_16_1_1473 32 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 68 263 (accept_3_2 31 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 68 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 68 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 68 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 263 (accept_3_2 28 68 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 263 (accept_3_2 25 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 263 (accept_3_2 22 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 263 (accept_3_2 19 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 263 (Polychromatic418967fa.accept_20_18_8_3_1_9071 18 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 263 (accept_3_2 16 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 263 (accept_3_2 13 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 263 (accept_3_2 10 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 263 (accept_3_2 7 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  263 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 263 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 263 (accept_3_2 4 68 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  68 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 263 (accept_3_2 1 68 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 263 (allA_of_3_0 67 67 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 263 (allA_succ_of_accept 65 66 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 263 (accept_3_2 64 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 263 (Polychromatic418967fa.accept_13_11_1_3_1_910 63 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 263 (accept_3_2 61 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 66 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 263 (accept_3_2 58 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 263 (Polychromatic418967fa.accept_13_4_1_3_1_3058 56 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 263 (accept_3_2 55 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 263 (Polychromatic418967fa.accept_13_2_1_3_1_419 54 66 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 263 (accept_3_2 52 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 263 (accept_3_2 49 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 66 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 263
  (Polychromatic418967fa.accept_10_7_6_3_1_927 47 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 263 (accept_3_2 46 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 263 (accept_3_2 43 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 66 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 263 (accept_3_2 40 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 263 (Polychromatic418967fa.accept_10_9_6_3_1_545 39 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 263 (accept_3_2 37 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 66 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 263 (accept_3_2 34 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 263 (accept_3_2 31 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 263 (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 66 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 263 (accept_3_2 28 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 263 (accept_3_2 25 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 66 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 263 (accept_3_2 22 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 263 (accept_3_2 19 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 66 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 263 (accept_3_2 16 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 263 (accept_3_2 13 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 263 (Polychromatic418967fa.accept_16_12_2_7_1_6853 12 66 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 263
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 263 (accept_3_2 10 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 66 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 263 (accept_3_2 7 66 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 66 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 66 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 263 (accept_3_2 4 66 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 263
  (Polychromatic418967fa.accept_25_3_16_13_1_16051 3 66 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 263 (Polychromatic418967fa.accept_13_2_1_3_1_419 2 66 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 263 (accept_3_2 1 66 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 263
  (allA_succ_of_accept 64 65 263 (accept_3_2 64 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 263 (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 263 (accept_3_2 61 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 263 (Polychromatic418967fa.accept_23_14_19_10_1_14323 60 65 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 263
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 59 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 263 (accept_3_2 58 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 263 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 263 (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 65 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 263 (accept_3_2 55 65 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 263
  (Polychromatic418967fa.accept_19_15_8_16_1_10745 53 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 65 263 (accept_3_2 52 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 65 263 (Polychromatic418967fa.accept_21_9_2_11_1_10112 51 65 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 263 (accept_3_2 49 65 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 48
  65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 263 (accept_3_2 46 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 263 (Polychromatic418967fa.accept_17_11_14_8_1_2729 45 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 263 (Polychromatic418967fa.accept_14_2_9_11_1_3054 44 65 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 263 (accept_3_2 43 65 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 263
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 263 (accept_3_2 40 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 263 (Polychromatic418967fa.accept_19_1_8_16_1_6488 39 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 263 (accept_3_2 37 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 263 (Polychromatic418967fa.accept_19_17_8_16_1_12029 36 65 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 263
  (Polychromatic418967fa.accept_20_15_5_3_1_1953 35 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 263 (accept_3_2 34 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 263 (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 263 (accept_3_2 31 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 263
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 263 (accept_3_2 28 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 263 (accept_3_2 25 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 263 (Polychromatic418967fa.accept_16_8_1_7_1_2355 24 65 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 263
  (Polychromatic418967fa.accept_17_6_14_8_1_3858 23 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 263 (accept_3_2 22 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 263 (Polychromatic418967fa.accept_20_1_5_3_1_7397 21 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 263 (accept_3_2 19 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 263
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 263 (accept_3_2 16 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 263 (Polychromatic418967fa.accept_19_15_8_16_1_10745 15 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 263 (accept_3_2 13 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 263
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 263 (accept_3_2 10 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 263 (Polychromatic418967fa.accept_19_9_8_16_1_5101 9 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 263 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 263 (accept_3_2 7 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 263 (accept_3_2 4 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  263 (Polychromatic418967fa.accept_15_3_5_8_1_1387 3 65 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 65 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 263 (accept_3_2 1 65 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 65 263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64
  263 (allA_of_3_0 64 64 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 263 (allA_succ_of_accept 62 63 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 263 (accept_3_2 61 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 263 (Polychromatic418967fa.accept_13_8_11_3_1_3053 60 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 263 (Polychromatic418967fa.accept_13_7_11_3_1_1540 59 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 263 (accept_3_2 58 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 63
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 263 (accept_3_2 55 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 263 (Polychromatic418967fa.accept_13_2_11_3_1_873 54 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 263 (Polychromatic418967fa.accept_11_9_8_10_1_934 53 63 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 263 (accept_3_2 52 63 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 263 (Polychromatic418967fa.accept_16_3_15_7_1_3417 51 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 263 (accept_3_2 49 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 263 (Polychromatic418967fa.accept_18_12_9_11_1_4370 48 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 263 (Polychromatic418967fa.accept_13_8_11_3_1_3053 47 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 263 (accept_3_2 46 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 63
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 263 (accept_3_2 43 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 263 (Polychromatic418967fa.accept_11_9_8_10_1_934 42 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 263 (Polychromatic418967fa.accept_13_2_11_3_1_873 41 63 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 263 (accept_3_2 40 63 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 263 (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 263 (accept_3_2 37 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 263 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 263 (Polychromatic418967fa.accept_15_5_3_8_1_748 35 63 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 263 (accept_3_2 34 63 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 263 (accept_3_2 31 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 263 (Polychromatic418967fa.accept_16_14_15_7_1_5655 30 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 263 (Polychromatic418967fa.accept_19_10_6_16_1_7964 29 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 263 (accept_3_2 28 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 263 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 63 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 263 (accept_3_2 25 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 263 (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 263 (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 263 (accept_3_2 22 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 63
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 263 (accept_3_2 19 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 263 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 263 (Polychromatic418967fa.accept_14_3_7_11_1_765 17 63 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 263 (accept_3_2 16 63 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 263 (Polychromatic418967fa.accept_13_2_11_3_1_873 15 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 263 (accept_3_2 13 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 263 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 263 (Polychromatic418967fa.accept_15_11_3_8_1_750 11 63 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 263 (accept_3_2 10 63 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 263 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 263 (accept_3_2 7 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  263 (Polychromatic418967fa.accept_16_6_15_7_1_1510 6 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 263 (Polychromatic418967fa.accept_13_5_11_3_1_902 5 63 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 263 (accept_3_2 4 63 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 263 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 63 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 263 (accept_3_2 1 63 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 263 (allA_succ_of_accept 61 62 263
  (accept_3_2 61 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 263
  (Polychromatic418967fa.accept_9_6_8_2_1_410 60 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 62 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 263 (accept_3_2 58 62 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 263 (Polychromatic418967fa.accept_12_8_2_11_1_246
  56 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 263 (accept_3_2 55
  62 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 263 (accept_3_2 52 62 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 62 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 50
  62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 263 (accept_3_2 49 62
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 263
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 62 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 263 (accept_3_2 46 62 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 263 (accept_3_2 43 62
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 263
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 263 (accept_3_2 40 62 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 62 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 38
  62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 263 (accept_3_2 37 62
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 263
  (Polychromatic418967fa.accept_11_3_7_10_1_180 36 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 62 263 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 62 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 263 (accept_3_2 34 62 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 62 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 32
  62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 263 (accept_3_2 31 62
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 263 (Polychromatic418967fa.accept_7_2_6_4_1_29
  30 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 263 (accept_3_2 28 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 62 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 263 (accept_3_2 25 62 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 62 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 263 (accept_3_2 22 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 62 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 263 (accept_3_2 19 62 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 263 (Polychromatic418967fa.accept_17_1_11_8_1_2725 18 62 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 263 (accept_3_2 16 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 62 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 263 (accept_3_2 13 62 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 62 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 263
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 263 (accept_3_2 10 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 62 263 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 62 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 263 (accept_3_2 7 62 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 62 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 62 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 263 (accept_3_2 4 62 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 62 263 (accept_3_2 1 62 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 263 (allA_of_3_0 61 61 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 263 (allA_succ_of_accept 59 60 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 263 (accept_3_2 58 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 263 (Polychromatic418967fa.accept_16_8_12_7_1_2399 56 60 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 263 (accept_3_2 55 60 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 263 (Polychromatic418967fa.accept_21_12_18_11_1_10051 54 60
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 263 (accept_3_2 52 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 263 (accept_3_2 49 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 60 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 263
  (Polychromatic418967fa.accept_21_5_18_11_1_7041 47 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 263 (accept_3_2 46 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 263 (Polychromatic418967fa.accept_17_11_9_8_1_5038 45 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 263 (accept_3_2 43 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 263 (Polychromatic418967fa.accept_19_4_3_16_1_5097 42 60 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 263 (accept_3_2 40 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 263 (Polychromatic418967fa.accept_27_11_6_20_1_12304 38 60 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 263 (accept_3_2 37 60 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 263 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 60
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 263 (accept_3_2 34 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 263 (Polychromatic418967fa.accept_13_7_8_3_1_1533 33 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 263 (accept_3_2 31 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 60 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 263
  (Polychromatic418967fa.accept_14_1_4_11_1_3036 29 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 263 (accept_3_2 28 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 263 (accept_3_2 25 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 263 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 60 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 263 (accept_3_2 22 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 263 (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 263 (accept_3_2 19 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 263 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 60 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 263 (accept_3_2 16 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 263 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 263 (accept_3_2 13 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 60 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 263 (accept_3_2 10 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 263 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 263 (accept_3_2 7 60 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 263 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 60 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 263 (accept_3_2 4 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  263 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 60 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 263 (Polychromatic418967fa.accept_16_2_12_7_1_3410 2 60 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 263 (accept_3_2 1 60 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 263
  (allA_succ_of_accept 58 59 263 (accept_3_2 58 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 263 (Polychromatic418967fa.accept_10_6_9_3_1_935 56 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 263 (accept_3_2 55 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 263 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 59 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 263 (accept_3_2 52 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 263 (accept_3_2 49 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 59 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 263
  (Polychromatic418967fa.accept_13_8_7_3_1_430 47 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 263 (accept_3_2 46 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 263 (Polychromatic418967fa.accept_19_7_2_16_1_1496 45 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 263 (accept_3_2 43 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 59 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 263 (accept_3_2 40 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 263 (Polychromatic418967fa.accept_11_5_4_10_1_524 38 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 263 (accept_3_2 37 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 263 (accept_3_2 34 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 263 (Polychromatic418967fa.accept_18_14_5_11_1_5676 32 59 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 263 (accept_3_2 31 59 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 59 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 263 (accept_3_2 28 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 263 (accept_3_2 25 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 263
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 263 (accept_3_2 22 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 263 (accept_3_2 19 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 263 (Polychromatic418967fa.accept_16_2_11_7_1_2352 18 59 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 263 (accept_3_2 16 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 263 (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 263 (accept_3_2 13 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 59 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 263
  (Polychromatic418967fa.accept_13_11_7_3_1_894 11 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 263 (accept_3_2 10 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 263 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 263 (accept_3_2 7 59 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 59 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 263
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 263 (accept_3_2 4 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  263 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 59 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 263 (Polychromatic418967fa.accept_16_2_11_7_1_2352 2 59 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 263 (accept_3_2 1 59 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 263))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 263 (allA_of_3_0
  58 58 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 263 (allA_succ_of_accept 56 57 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 263 (accept_3_2 55 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 263 (accept_3_2 52 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 57 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 263 (accept_3_2 49 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 263 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 263 (accept_3_2 46 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 57 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 263 (accept_3_2 43 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 263 (accept_3_2 40 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 57 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 263 (accept_3_2 37 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 263 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 263 (accept_3_2 34 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 263 (accept_3_2 31 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 263 (Polychromatic418967fa.accept_16_13_9_7_1_4532 29 57 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 263 (accept_3_2 28 57 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 57 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 263 (accept_3_2 25 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 263 (accept_3_2 22 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 263 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 57 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 263 (accept_3_2 19 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 263 (accept_3_2 16 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 263 (accept_3_2 13 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 263 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 263 (accept_3_2 10 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 263 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 57 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 263 (accept_3_2 7 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 57 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 263 (accept_3_2 4 57 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 263 (accept_3_2 1 57 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 263 (allA_succ_of_accept 55 56 263 (accept_3_2 55 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 263 (Polychromatic418967fa.accept_17_3_5_8_1_1687 54 56 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 263 (Polychromatic418967fa.accept_11_9_1_10_1_920 53 56 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 263 (accept_3_2 52 56 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 263 (accept_3_2 49 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 263 (Polychromatic418967fa.accept_10_7_6_3_1_927 47 56 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 263 (accept_3_2 46 56 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 263
  (Polychromatic418967fa.accept_16_12_8_7_1_4530 44 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 263 (accept_3_2 43 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 263 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 263 (Polychromatic418967fa.accept_16_9_8_7_1_4529 41 56 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 263 (accept_3_2 40 56 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 263
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 263 (accept_3_2 37 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 263 (Polychromatic418967fa.accept_16_4_8_7_1_3396 36 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 263 (Polychromatic418967fa.accept_11_2_1_10_1_196 35 56 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 263 (accept_3_2 34 56 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 263
  (Polychromatic418967fa.accept_18_14_2_11_1_4384 32 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 263 (accept_3_2 31 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 263 (Polychromatic418967fa.accept_17_13_5_8_1_896 30 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 263 (Polychromatic418967fa.accept_10_9_6_3_1_545 29 56 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 263 (accept_3_2 28 56 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 263 (accept_3_2 25 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 263 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 263 (Polychromatic418967fa.accept_21_2_14_11_1_7060 23 56 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 263 (accept_3_2 22 56 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 263
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 263 (accept_3_2 19 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 263 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 56 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 263 (accept_3_2 16 56 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 263 (accept_3_2 13 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 263 (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 263 (Polychromatic418967fa.accept_22_11_12_21_1_14520 11 56 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 263 (accept_3_2 10 56 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 263
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 263 (accept_3_2 7 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  263 (Polychromatic418967fa.accept_21_6_14_11_1_10103 6 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 56 263 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 56 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 263 (accept_3_2 4 56 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 263
  (Polychromatic418967fa.accept_11_2_1_10_1_196 2 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 263 (accept_3_2 1 56 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 263 (allA_of_3_0 55 55 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 54 263 (allA_succ_of_accept 53 54 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 263 (accept_3_2 52 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  54 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 54 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 54 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 263 (accept_3_2 49 54 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 54 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 263
  (Polychromatic418967fa.accept_10_7_4_3_1_560 47 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 263 (accept_3_2 46 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  54 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 54 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 54 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 263 (accept_3_2 43 54 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 263 (Polychromatic418967fa.accept_22_20_10_21_1_9863 42 54 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 54 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 263 (accept_3_2 40 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  54 263 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 54 263 (Polychromatic418967fa.accept_13_12_2_3_1_1527 38 54 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 263 (accept_3_2 37 54 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 54 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 54 263
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 263 (accept_3_2 34 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  54 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 54 263 (Polychromatic418967fa.accept_15_2_9_8_1_736 32 54 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 263 (accept_3_2 31 54 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 54 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 263 (accept_3_2 28 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  54 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 54 263 (Polychromatic418967fa.accept_21_5_12_11_1_5429 26 54 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 263 (accept_3_2 25 54 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 263 (Polychromatic418967fa.accept_13_11_2_3_1_883 24 54 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 54 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 263 (accept_3_2 22 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  54 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 54 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 54 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 263 (accept_3_2 19 54 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 263 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 54 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 54 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 263 (accept_3_2 16 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  54 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 54 263 (Polychromatic418967fa.accept_13_1_2_3_1_911 14 54 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 263 (accept_3_2 13 54 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 263 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 54 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 263
  (Polychromatic418967fa.accept_13_11_2_3_1_883 11 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 263 (accept_3_2 10 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  54 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 54 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 54 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 263 (accept_3_2 7 54 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 54 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 54 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 263 (accept_3_2 4 54 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 263 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3
  54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 263 (accept_3_2 1 54 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 263 (allA_succ_of_accept 52 53 263 (accept_3_2
  52 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 263
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 263 (accept_3_2 49 53 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 263
  (Polychromatic418967fa.accept_31_16_22_15_1_16050 47 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 53 263 (accept_3_2 46 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 53 263 (Polychromatic418967fa.accept_11_1_9_10_1_184 45 53 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 263 (Polychromatic418967fa.accept_13_5_1_3_1_878 44 53 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 263 (accept_3_2 43 53 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 263 (accept_3_2 40 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 263 (accept_3_2 37 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 263 (Polychromatic418967fa.accept_20_16_13_3_1_5974 36 53 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 263
  (Polychromatic418967fa.accept_22_13_9_21_1_9862 35 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 263 (accept_3_2 34 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 263 (accept_3_2 31 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 263
  (Polychromatic418967fa.accept_25_4_3_13_1_16049 29 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 263 (accept_3_2 28 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 263 (Polychromatic418967fa.accept_16_11_5_7_1_2395 27 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 263 (accept_3_2 25 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 53 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 263 (accept_3_2 22 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 263 (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 263 (accept_3_2 19 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 263
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 263 (accept_3_2 16 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 263 (accept_3_2 13 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 53 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 263
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 263 (accept_3_2 10 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 263 (Polychromatic418967fa.accept_28_9_25_11_1_16048 9 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 263 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 263 (accept_3_2 7 53 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 263 (accept_3_2 4 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  263 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 53 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 263 (accept_3_2 1 53 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 263))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 263 (allA_of_3_0 52 52
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 263 (allA_succ_of_accept 50 51 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 263 (accept_3_2 49 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 51 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 263 (accept_3_2 46 51 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 51 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 263 (accept_3_2 43 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 263 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 51 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 263 (accept_3_2 40 51 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 51 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 263 (accept_3_2 37 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 51 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 263 (accept_3_2 34 51 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 51 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 263 (accept_3_2 31 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 263 (Polychromatic418967fa.accept_15_14_6_8_1_1410 29 51 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 263 (accept_3_2 28 51 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 263 (accept_3_2 25 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 263 (Polychromatic418967fa.accept_18_6_15_11_1_3141 24 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 51 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 263 (accept_3_2 22 51 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 263 (accept_3_2 19 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 263 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 51 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 263 (accept_3_2 16 51 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 263 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 51 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 263 (accept_3_2 13 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 263 (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 51 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 263 (accept_3_2 10 51 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 51 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 263 (accept_3_2 7 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 51 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 263 (accept_3_2 4 51 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 51 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 263 (accept_3_2 1 51 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 263)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 263 (allA_succ_of_accept 49 50 263 (accept_3_2 49 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 50 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 50 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 263 (accept_3_2 46 50 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 263 (accept_3_2 43 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 263 (accept_3_2 40 50 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 263 (accept_3_2 37 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 263 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 50 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 263 (accept_3_2 34 50 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 263 (accept_3_2 31 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 263 (accept_3_2 28 50 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 50 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 263 (accept_3_2 25 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 263 (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 50 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 263 (accept_3_2 22 50 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 263 (accept_3_2 19 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 263 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 263 (accept_3_2 16 50 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 50 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 263
  (Polychromatic418967fa.accept_13_1_11_3_1_901 14 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 263 (accept_3_2 13 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 263 (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 50 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 263 (accept_3_2 10 50 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 263 (accept_3_2 7 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  263 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 263 (accept_3_2 4 50 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 50 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 263 (Polychromatic418967fa.accept_13_2_11_3_1_873 2
  50 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 263 (accept_3_2 1 50 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 263)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 263 (allA_of_3_0 49 49 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 263 (allA_succ_of_accept 47 48
  263 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 263 (accept_3_2 46 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 48 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 263 (accept_3_2 43 48 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 48 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 263 (accept_3_2 40 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 263 (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 48 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 263 (accept_3_2 37 48 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 263 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 48 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 263 (accept_3_2 34 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 48 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 263 (accept_3_2 31 48 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 48 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 263
  (Polychromatic418967fa.accept_25_4_23_13_1_16047 29 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 48 263 (accept_3_2 28 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 48 263 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 48 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 48 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 263 (accept_3_2 25 48 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24
  48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 263 (accept_3_2 22 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 263 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 263 (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 48 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 263 (accept_3_2 19 48 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 263 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 48 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 263 (accept_3_2 16 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 48 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 263 (accept_3_2 13 48 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 48 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 263
  (Polychromatic418967fa.accept_10_1_8_3_1_947 11 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 263 (accept_3_2 10 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 48 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 263 (accept_3_2 7 48 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 48 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 263 (accept_3_2 4 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 48 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 263 (accept_3_2 1 48 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 263)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 263 (allA_succ_of_accept 46
  47 263 (accept_3_2 46 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 47 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 263 (accept_3_2 43 47 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 263 (Polychromatic418967fa.accept_19_4_9_16_1_3811 42 47 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 263
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 263 (accept_3_2 40 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 263 (Polychromatic418967fa.accept_15_9_2_8_1_1379 39 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 263 (Polychromatic418967fa.accept_16_6_15_7_1_1510 38 47 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 263 (accept_3_2 37 47 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 263 (accept_3_2 34 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 263 (Polychromatic418967fa.accept_13_7_8_3_1_1533 33 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 263 (Polychromatic418967fa.accept_17_15_13_8_1_7603 32 47 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 263 (accept_3_2 31 47 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 47 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 263 (accept_3_2 28 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 263 (Polychromatic418967fa.accept_10_6_7_3_1_547 26 47 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 263 (accept_3_2 25 47 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 263 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 47 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 263 (accept_3_2 22 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 263 (Polychromatic418967fa.accept_15_6_2_8_1_2223 21 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 47 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 263 (accept_3_2 19 47 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 263 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 47 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 263
  (Polychromatic418967fa.accept_21_17_5_11_1_7028 17 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 263 (accept_3_2 16 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 263 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 47 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 263 (accept_3_2 13 47 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 263 (Polychromatic418967fa.accept_19_12_9_16_1_5086 12 47 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 263
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 263 (accept_3_2 10 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 47 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 263 (accept_3_2 7 47 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 47 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 263
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 263 (accept_3_2 4 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  263 (Polychromatic418967fa.accept_16_3_15_7_1_3417 3 47 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 47 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 47 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 263 (accept_3_2 1 47 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 47 263))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 263 (allA_of_3_0 46
  46 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 263 (allA_succ_of_accept 44 45 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 263 (accept_3_2 43 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 45 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 263 (accept_3_2 40 45 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 45 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 263 (accept_3_2 37 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 263 (Polychromatic418967fa.accept_11_2_1_10_1_196 35 45 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 263 (accept_3_2 34 45 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 263 (Polychromatic418967fa.accept_18_15_9_11_1_4371 33 45 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 263 (accept_3_2 31 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 45 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 263 (accept_3_2 28 45 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 45 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 263 (accept_3_2 25 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 263 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 263 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 45 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 263 (accept_3_2 22 45 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 263 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 45
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 263 (accept_3_2 19 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 263 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 45 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 263 (accept_3_2 16 45 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 45 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 263 (accept_3_2 13 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 263 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 263 (Polychromatic418967fa.accept_22_11_1_21_1_6560 11 45 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 263 (accept_3_2 10 45 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 263 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 45 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 263 (accept_3_2 7 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 263 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 45 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 263 (accept_3_2 4 45 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 45 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 263 (accept_3_2 1 45 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 263))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  263 (allA_succ_of_accept 43 44 263 (accept_3_2 43 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 263 (accept_3_2 40 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 263 (accept_3_2 37 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 263 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 263 (accept_3_2 34 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 263 (accept_3_2 31 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 263 (Polychromatic418967fa.accept_10_9_4_3_1_539 29 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 263 (accept_3_2 28 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 263 (accept_3_2 25 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 263 (accept_3_2 22 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 263
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 263 (accept_3_2 19 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 263 (Polychromatic418967fa.accept_16_2_12_7_1_3410 18 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 263 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 263 (accept_3_2 16 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 263 (accept_3_2 13 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 263 (accept_3_2 10 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 263
  (Polychromatic418967fa.accept_13_8_5_3_1_427 8 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 263 (accept_3_2 7 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 44 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 263 (accept_3_2 4 44 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  44 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 263 (accept_3_2 1 44 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 263)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  263 (allA_of_3_0 43 43 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 263 (allA_succ_of_accept 41 42 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 263 (accept_3_2 40 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 263 (Polychromatic418967fa.accept_20_18_2_3_1_3169 38 42 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 263 (accept_3_2 37 42 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 263 (Polychromatic418967fa.accept_23_13_19_10_1_14319 36 42
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 263 (accept_3_2 34 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 42 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 263 (accept_3_2 31 42 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 42 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 263 (accept_3_2 28 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 263 (Polychromatic418967fa.accept_22_5_20_21_1_6539 27 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 42 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 263 (accept_3_2 25 42 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 263 (Polychromatic418967fa.accept_25_24_17_13_1_16046 24 42 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 263 (accept_3_2 22 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 263 (Polychromatic418967fa.accept_15_5_12_8_1_3168 20 42 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 263 (accept_3_2 19 42 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 263 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 42 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 263 (accept_3_2 16 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 263 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 42 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 263 (accept_3_2 13 42 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 42 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 263
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 263 (accept_3_2 10 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 42 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 263 (accept_3_2 7 42 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 42 263 (Polychromatic418967fa.accept_23_6_19_10_1_14322 6 42 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 263 (accept_3_2 4 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 42 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 263 (Polychromatic418967fa.accept_19_2_4_16_1_7984 2 42 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 263 (accept_3_2 1 42 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 263)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 263 (allA_succ_of_accept 40 41
  263 (accept_3_2 40 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 263
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 263 (accept_3_2 37 41 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 263 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 41 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 263 (accept_3_2 34 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 263 (Polychromatic418967fa.accept_10_2_1_3_1_233 32 41 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 263 (accept_3_2 31 41 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 263
  (Polychromatic418967fa.accept_16_13_9_7_1_4532 29 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 263 (accept_3_2 28 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 263 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 263 (accept_3_2 25 41 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 41 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 263 (accept_3_2 22 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 263 (Polychromatic418967fa.accept_11_9_8_10_1_934 20 41 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 263 (accept_3_2 19 41 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 263 (accept_3_2 16 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 263 (accept_3_2 13 41 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 263
  (Polychromatic418967fa.accept_13_11_2_3_1_883 11 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 263 (accept_3_2 10 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 41 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 263 (accept_3_2 7 41 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 263 (accept_3_2 4 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 41 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 263 (accept_3_2 1 41 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 263))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 263 (allA_of_3_0 40 40 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 263 (allA_succ_of_accept 38 39 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 263 (accept_3_2 37 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 263 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 39 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 263 (accept_3_2 34 39 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 39 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 263 (accept_3_2 31 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 263 (Polychromatic418967fa.accept_17_13_5_8_1_896 30 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 263 (Polychromatic418967fa.accept_15_14_9_8_1_3165 29 39 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 263 (accept_3_2 28 39 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 263 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 39
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 263 (accept_3_2 25 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 39 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 263 (accept_3_2 22 39 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 39 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 263 (accept_3_2 19 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 263 (Polychromatic418967fa.accept_15_3_9_8_1_3164 18 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 39 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 263 (accept_3_2 16 39 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 39 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 263 (accept_3_2 13 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 263 (Polychromatic418967fa.accept_17_12_5_8_1_7680 12 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 263 (Polychromatic418967fa.accept_24_11_15_23_1_3964 11 39 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 263 (accept_3_2 10 39 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 39 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 263
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 263 (accept_3_2 7 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  263 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 39 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 39 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 263 (accept_3_2 4 39 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 263 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 39 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 263 (accept_3_2 1 39 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 263))))))))))))))))))))))))))))))))))))))) (allB_succ 38 263
  (allA_succ_of_accept 37 38 263 (accept_3_2 37 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 263 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 38 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 263 (accept_3_2 34 38 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 263
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 263 (accept_3_2 31 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 263 (Polychromatic418967fa.accept_13_4_12_3_1_2999 30 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 263 (accept_3_2 28 38 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 263
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 263 (accept_3_2 25 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 263 (Polychromatic418967fa.accept_17_7_4_8_1_7678 24 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 263 (Polychromatic418967fa.accept_21_2_17_11_1_7037 23 38 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 263 (accept_3_2 22 38 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 263
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 263 (accept_3_2 19 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 263 (Polychromatic418967fa.accept_17_1_4_8_1_5049 18 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 263 (accept_3_2 16 38 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 38 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 263
  (Polychromatic418967fa.accept_18_14_2_11_1_4384 14 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 263 (accept_3_2 13 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 263 (Polychromatic418967fa.accept_17_12_4_8_1_5073 12 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 263 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 38 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 263 (accept_3_2 10 38 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 263 (accept_3_2 7 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 38 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 263 (accept_3_2 4 38 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 263 (Polychromatic418967fa.accept_13_2_12_3_1_415 2
  38 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 263 (accept_3_2 1 38 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 263)))))))))))))))))))))))))))))))))))))) (allB_succ 37 263
  (allA_of_3_0 37 37 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 263 (allA_succ_of_accept 35 36 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 263 (accept_3_2 34 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 263 (Polychromatic418967fa.accept_13_6_10_3_1_897 32 36 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 263 (accept_3_2 31 36 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 263 (Polychromatic418967fa.accept_16_14_4_7_1_2380 30 36 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 263
  (Polychromatic418967fa.accept_10_9_6_3_1_545 29 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 263 (accept_3_2 28 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 36 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 263 (accept_3_2 25 36 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 36 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 263
  (Polychromatic418967fa.accept_22_1_14_21_1_16045 23 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 36 263 (accept_3_2 22 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 36 263 (Polychromatic418967fa.accept_19_2_17_16_1_6481 21 36 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 263 (Polychromatic418967fa.accept_13_7_10_3_1_1505 20 36
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 263 (accept_3_2 19 36 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394
  18 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 263 (accept_3_2 16 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 263 (Polychromatic418967fa.accept_13_2_10_3_1_1538 15 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 263 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 36 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 263 (accept_3_2 13 36 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 36 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 263
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 263 (accept_3_2 10 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 263 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 263 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 36 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 263 (accept_3_2 7 36 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 263 (Polychromatic418967fa.accept_13_6_10_3_1_897 6 36 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 263 (accept_3_2 4 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 263 (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 36 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 263 (accept_3_2 1 36 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 263)))))))))))))))))))))))))))))))))))) (allB_succ 35 263 (allA_succ_of_accept 34 35 263
  (accept_3_2 34 35 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 263
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 35 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 263 (accept_3_2 31 35 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 35 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 263 (Polychromatic418967fa.accept_15_14_5_8_1_3175
  29 35 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 263 (accept_3_2 28
  35 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 263
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 35 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 263 (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 35 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 263 (accept_3_2 25 35 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 23
  35 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 263 (accept_3_2 22 35
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 263
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 35 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 35 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 263 (accept_3_2 19 35 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 263 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 35 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 263 (Polychromatic418967fa.accept_10_7_5_3_1_542
  17 35 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 263 (accept_3_2 16
  35 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 263
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 35 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 35 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 263 (accept_3_2 13 35 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 263 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 263 (Polychromatic418967fa.accept_15_11_5_8_1_3157
  11 35 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 263 (accept_3_2 10
  35 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 263
  (Polychromatic418967fa.accept_16_9_3_7_1_6883 9 35 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 263 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 35 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 263 (accept_3_2 7 35 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 35 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 5
  35 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 263 (accept_3_2 4 35 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 3
  35 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 263
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 35 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 263 (accept_3_2 1 35 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  263))))))))))))))))))))))))))))))))))) (allB_succ 34 263 (allA_of_3_0 34 34 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 263 (allA_succ_of_accept 32 33 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 263 (accept_3_2 31 33 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  33 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 263
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 263 (accept_3_2 28 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 263 (accept_3_2 25 33 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 263 (Polychromatic418967fa.accept_13_11_7_3_1_894 24 33 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 263
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 263 (accept_3_2 22 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 263 (accept_3_2 19 33 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 263
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 263 (accept_3_2 16 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 263 (accept_3_2 13 33 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 263
  (Polychromatic418967fa.accept_13_11_7_3_1_894 11 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 263 (accept_3_2 10 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 263 (accept_3_2 7 33 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 263 (accept_3_2 4 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 33 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 263 (accept_3_2 1 33 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 263))))))))))))))))))))))))))))))))) (allB_succ 32 263 (allA_succ_of_accept 31 32 263
  (accept_3_2 31 32 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 263
  (Polychromatic418967fa.accept_9_3_5_2_1_28 30 32 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 263 (Polychromatic418967fa.accept_14_1_4_11_1_3036 29 32 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 263 (accept_3_2 28 32 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 26
  32 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 263 (accept_3_2 25 32
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 263
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 32 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 263 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 32 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 263 (accept_3_2 22 32 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 263
  (Polychromatic418967fa.accept_18_2_14_11_1_3139 20 32 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 263 (accept_3_2 19 32 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 263 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 32 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 32 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 263 (accept_3_2 16 32 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 32 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 263 (accept_3_2 13 32 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 32 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 263 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 32 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 263 (accept_3_2 10 32 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 32 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 263 (accept_3_2 7 32 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  263 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 32 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 263 (Polychromatic418967fa.accept_10_5_2_3_1_239 5 32 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 263 (accept_3_2 4 32 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 263 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  32 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 263 (accept_3_2 1 32 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 263)))))))))))))))))))))))))))))))) (allB_succ 31 263
  (allA_of_3_0 31 31 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 263 (allA_succ_of_accept 29 30 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 263 (accept_3_2 28 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 30 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 263 (accept_3_2 25 30 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 30 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 263 (accept_3_2 22 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 30 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 263 (accept_3_2 19 30 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 263 (Polychromatic418967fa.accept_21_18_9_11_1_7082 18 30 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 263 (accept_3_2 16 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 263 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 30 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 263 (accept_3_2 13 30 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 30 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 263
  (Polychromatic418967fa.accept_20_11_10_3_1_10529 11 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 30 263 (accept_3_2 10 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 30 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 263 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 30 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 263 (accept_3_2 7 30 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6
  30 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 263 (accept_3_2 4 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  263 (Polychromatic418967fa.accept_17_3_13_8_1_11337 3 30 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 30 263 (Polychromatic418967fa.accept_19_2_11_16_1_6525 2 30 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 263 (accept_3_2 1 30 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 30 263)))))))))))))))))))))))))))))) (allB_succ 29 263 (allA_succ_of_accept 28 29 263
  (accept_3_2 28 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 263
  (Polychromatic418967fa.accept_17_10_12_8_1_2748 27 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 263 (accept_3_2 25 29 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 263 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 29 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 263
  (Polychromatic418967fa.accept_19_4_10_16_1_6531 23 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 263 (accept_3_2 22 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 263 (Polychromatic418967fa.accept_15_6_14_8_1_245 21 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 263 (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 29 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 263 (accept_3_2 19 29 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 263
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 263 (accept_3_2 16 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 263 (Polychromatic418967fa.accept_20_15_9_3_1_7435 15 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 263 (accept_3_2 13 29 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 263
  (Polychromatic418967fa.accept_22_11_7_21_1_9879 11 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 263 (accept_3_2 10 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 263 (Polychromatic418967fa.accept_15_9_14_8_1_1396 9 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 263 (Polychromatic418967fa.accept_19_8_10_16_1_9418 8 29 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 263 (accept_3_2 7 29 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 263 (accept_3_2 4 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 29 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 263 (accept_3_2 1 29 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 263))))))))))))))))))))))))))))) (allB_succ 28 263 (allA_of_3_0 28 28 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 263 (allA_succ_of_accept 26 27 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 263 (accept_3_2 25 27 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 24
  27 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 263
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 27 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 263 (accept_3_2 22 27 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 27 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 263 (accept_3_2 19 27 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 263 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 27 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 27 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 263 (accept_3_2 16 27 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 263 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 27 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 263 (accept_3_2 13 27 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 263 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 263
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 27 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 263 (accept_3_2 10 27 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 27 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 263 (accept_3_2 7 27 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 263 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 27 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 27 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 263 (accept_3_2 4 27 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  263 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 263 (accept_3_2 1 27 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 263))))))))))))))))))))))))))) (allB_succ 26 263 (allA_succ_of_accept 25 26 263 (accept_3_2
  25 26 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 263
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 26 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 26 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 263 (accept_3_2 22 26 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  26 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 263 (accept_3_2 19 26
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 263
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 26 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 263 (accept_3_2 16 26 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 26 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 263 (Polychromatic418967fa.accept_9_5_8_2_1_409 14
  26 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 263 (accept_3_2 13 26
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 263
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 26 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 26 263 (Polychromatic418967fa.accept_17_11_9_8_1_5038 11 26 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 263 (accept_3_2 10 26 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 26 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 8
  26 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 263 (accept_3_2 7 26 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 6
  26 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 263
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 263 (accept_3_2 4 26 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 26 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 263 (accept_3_2 1 26 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 263)))))))))))))))))))))))))) (allB_succ 25 263 (allA_of_3_0 25 25 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 263 (allA_succ_of_accept 23 24 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 23
  24 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 263 (accept_3_2 22 24
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 263
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 24 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 24 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 263 (accept_3_2 19 24 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 24 263 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 24 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 263 (Polychromatic418967fa.accept_9_8_6_2_1_744 17
  24 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 263 (accept_3_2 16 24
  263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 24 263 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 24 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 263 (accept_3_2 13 24 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 24 263 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 24 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 263
  (Polychromatic418967fa.accept_19_11_5_16_1_1456 11 24 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 263 (accept_3_2 10 24 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  24 263 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 24 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 24 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 24 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 263 (accept_3_2 7 24 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 263 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 24 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 263
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 24 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 263 (accept_3_2 4 24 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24
  263 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 263 (Polychromatic418967fa.accept_13_2_11_3_1_873 2 24 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 263 (accept_3_2 1 24 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 263)))))))))))))))))))))))) (allB_succ 23 263 (allA_succ_of_accept 22 23 263 (accept_3_2 22
  23 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 263
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 23 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 23 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 263 (accept_3_2 19 23 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 263 (Polychromatic418967fa.accept_25_18_23_13_1_16044 18 23 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 263
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 23 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 263 (accept_3_2 16 23 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 23 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 263 (Polychromatic418967fa.accept_17_14_6_8_1_7688 14 23 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 263 (accept_3_2 13 23 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 263
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 23 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 263 (accept_3_2 10 23 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 263 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 23 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 263 (accept_3_2 7 23 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 263 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 23 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 263
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 23 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 263 (accept_3_2 4 23 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  263 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 23 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 263 (Polychromatic418967fa.accept_11_2_1_10_1_196 2 23 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 263 (accept_3_2 1 23 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 263))))))))))))))))))))))) (allB_succ 22 263 (allA_of_3_0 22 22 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 21 263 (allA_succ_of_accept 20 21 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 263 (accept_3_2 19 21 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  21 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 263
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 21 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 263 (accept_3_2 16 21 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 263 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 263 (accept_3_2 13 21 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 263 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 21 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 263
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 21 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 263 (accept_3_2 10 21 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 263 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 21 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 263 (accept_3_2 7 21 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 21 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 263 (accept_3_2 4 21 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  263 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 21 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 263 (accept_3_2 1 21 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 263))))))))))))))))))))) (allB_succ 20 263 (allA_succ_of_accept 19 20 263
  (accept_3_2 19 20 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 263
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 20 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 263 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 20 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 263 (accept_3_2 16 20 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 263 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 20 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 263 (accept_3_2 13
  20 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 20 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 20 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 263 (accept_3_2 10 20 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 263 (Polychromatic418967fa.accept_11_8_9_10_1_503 8
  20 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 263 (accept_3_2 7 20 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 263 (Polychromatic418967fa.accept_21_6_20_11_1_7067
  6 20 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 263
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 20 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 263 (accept_3_2 4 20 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 20 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 263 (accept_3_2 1 20 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 263)))))))))))))))))))) (allB_succ 19 263 (allA_of_3_0 19 19 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 263 (allA_succ_of_accept 17 18 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 263 (accept_3_2 16 18 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 263 (Polychromatic418967fa.accept_10_5_8_3_1_229
  15 18 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 263
  (Polychromatic418967fa.accept_11_3_7_10_1_180 14 18 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 263 (accept_3_2 13 18 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 263 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 18 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 263 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 18 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 263 (accept_3_2 10 18 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 263
  (Polychromatic418967fa.accept_13_8_5_3_1_427 8 18 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 263 (accept_3_2 7 18 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  263 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 18 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 263 (accept_3_2 4 18 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 263 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 18 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 263 (Polychromatic418967fa.accept_13_2_5_3_1_406 2
  18 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 263 (accept_3_2 1 18 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 263)))))))))))))))))) (allB_succ 17 263 (allA_succ_of_accept 16
  17 263 (accept_3_2 16 17 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 263
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 17 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 263 (accept_3_2 13 17 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 263 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 17 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 263
  (Polychromatic418967fa.accept_23_11_17_10_1_16043 11 17 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 17 263 (accept_3_2 10 17 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 17 263 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 17 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 263 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 17 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 263 (accept_3_2 7 17 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 263
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 17 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 263 (accept_3_2 4 17 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  263 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 17 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 263 (accept_3_2 1 17 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 263))))))))))))))))) (allB_succ 16 263 (allA_of_3_0 16 16 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 15 263 (allA_succ_of_accept 14 15 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 263 (accept_3_2 13 15 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 12
  15 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 263
  (Polychromatic418967fa.accept_13_11_2_3_1_883 11 15 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 263 (accept_3_2 10 15 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  15 263 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 15 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 15 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 263 (accept_3_2 7 15 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 263 (Polychromatic418967fa.accept_16_6_15_7_1_1510 6 15 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 263
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 15 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 263 (accept_3_2 4 15 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15
  263 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 263 (accept_3_2 1 15 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 15 263))))))))))))))) (allB_succ 14 263 (allA_succ_of_accept 13 14 263 (accept_3_2 13 14 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 12
  14 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 263
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 14 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 263 (accept_3_2 10 14 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 14 263 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 14 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 263 (accept_3_2 7 14 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 14 263 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 14 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 263 (accept_3_2 4 14 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 263
  (Polychromatic418967fa.accept_13_2_1_3_1_419 2 14 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 263 (accept_3_2 1 14 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  263)))))))))))))) (allB_succ 13 263 (allA_of_3_0 13 13 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 263
  (allA_succ_of_accept 11 12 263 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 12 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 263 (accept_3_2 10 12 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 263 (Polychromatic418967fa.accept_7_1_5_4_1_134 8
  12 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 263 (accept_3_2 7 12 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 263 (Polychromatic418967fa.accept_7_6_5_4_1_297 6
  12 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 263
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 12 263 (accept_3_2 4 12 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12
  263 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 12 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 263 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 12 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 263 (accept_3_2 1 12 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 263)))))))))))) (allB_succ 11 263 (allA_succ_of_accept 10 11 263 (accept_3_2 10 11 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 263 (Polychromatic418967fa.accept_17_9_11_8_1_5077
  9 11 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 263
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 11 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 263 (accept_3_2 7 11 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  263 (Polychromatic418967fa.accept_19_6_11_16_1_9391 6 11 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 11 263 (Polychromatic418967fa.accept_13_5_11_3_1_902 5 11 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 263 (accept_3_2 4 11 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 263 (Polychromatic418967fa.accept_15_3_11_8_1_4186 3 11 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 263
  (Polychromatic418967fa.accept_10_2_1_3_1_233 2 11 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 263 (accept_3_2 1 11 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  263))))))))))) (allB_succ 10 263 (allA_of_3_0 10 10 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 263
  (allA_succ_of_accept 8 9 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 263 (accept_3_2 7 9 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 263 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 263 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 263 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 9
  263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 263 (accept_3_2 4 9 263
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 263 (Polychromatic418967fa.accept_12_3_9_11_1_231 3
  9 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 263 (accept_3_2 1 9 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 263)))))))))
  (allB_succ 8 263 (allA_succ_of_accept 7 8 263 (accept_3_2 7 8 263 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 263 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 8 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 263 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 8 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 263 (accept_3_2 4 8 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 263 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 263
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 8 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 263 (accept_3_2 1 8 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 263))))))))
  (allB_succ 7 263 (allA_of_3_0 7 7 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 263 (allA_succ_of_accept 5
  6 263 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 263 (accept_3_2 4 6 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 263
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 263 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 6 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 263 (accept_3_2 1 6 263 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 263)))))) (allB_succ 5 263 (allA_succ_of_accept 4 5 263 (accept_3_2 4 5 263 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 263 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 5 263
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 263
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 263 (accept_3_2 1 5 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 263)))))
  (allB_succ 4 263 (allA_of_3_0 4 4 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 263 (allA_succ_of_accept 2
  3 263 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 263 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 263 (accept_3_2 1 3 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 263)))
  (allB_succ 2 263 (allA_succ_of_accept 1 2 263 (accept_3_2 1 2 263 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  263)) (allB_two
  263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


