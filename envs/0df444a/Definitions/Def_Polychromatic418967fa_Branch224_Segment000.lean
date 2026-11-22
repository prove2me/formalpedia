-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch224_Segment000
-- name    : Polychromatic418967fa_Branch224_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:34:18.430054+00:00
-- url     : https://prove2.me/theorems/9afa22b8-edad-4527-8369-507bb076c253
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

def Polychromatic418967fa.branch_224_segment_000 : allB 125 224 :=
  allB_succ' 101 124 224 (Eq.refl Bool.true) (allA_of_3_0 101 124 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 102 123 224 (Eq.refl Bool.true) (allA_succ_of_accept 101 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 123 224 (accept_3_2 100 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 123 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 99 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 123 224 (Polychromatic418967fa.accept_17_13_4_3_1_1446 98 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 224 (accept_3_2 97 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 224 (Polychromatic418967fa.accept_13_5_6_3_1_868 96 123
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 123 224 (accept_3_2 94 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 123 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 123 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 92 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 224 (accept_3_2 91 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 224 (accept_3_2 88 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 123 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 87 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 123 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 86 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 224 (accept_3_2 85 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 123 224 (accept_3_2 82 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 123 224 (Polychromatic418967fa.accept_17_13_4_3_1_1446 81 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 123 224 (Polychromatic418967fa.accept_19_4_9_15_1_6405 80 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 224 (accept_3_2 79 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 123
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 224 (accept_3_2 76 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 123 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 123 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 224 (accept_3_2 73 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 72 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 123 224 (accept_3_2 70 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 123 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 69 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 123 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 224 (accept_3_2 67 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 123 224 (accept_3_2 64 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 123 224 (Polychromatic418967fa.accept_19_6_9_15_1_3694 63 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 123 224 (Polychromatic418967fa.accept_13_10_6_3_1_1515 62 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 224 (accept_3_2 61 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 224 (Polychromatic418967fa.accept_19_3_9_15_1_9240 60 123
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 224 (accept_3_2 58 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 123 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 123 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 224 (accept_3_2 55 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 224 (accept_3_2 52 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 123 224 (Polychromatic418967fa.accept_19_13_9_15_1_11989 51 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 224 (accept_3_2 49 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 123 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 224 (accept_3_2 46 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 224 (Polychromatic418967fa.accept_22_1_13_4_1_10190 45 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 123 224 (Polychromatic418967fa.accept_13_5_6_3_1_868 44 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 224 (accept_3_2 43 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 224 (Polychromatic418967fa.accept_11_9_2_4_1_707 42 123
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 224 (accept_3_2 40 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 224 (accept_3_2 37 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 224 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 123 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 224 (accept_3_2 34 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 224 (Polychromatic418967fa.accept_17_16_4_3_1_3429 33 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 224 (accept_3_2 31 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 224 (accept_3_2 28 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 224 (Polychromatic418967fa.accept_15_11_3_14_1_971 26 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 224 (accept_3_2 25 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 224 (Polychromatic418967fa.accept_17_7_4_3_1_3456 24 123
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 224 (accept_3_2 22 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 224 (accept_3_2 19 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 224 (accept_3_2 16 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 224 (Polychromatic418967fa.accept_21_15_18_14_1_5632 15 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 224 (accept_3_2 13 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 123 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 224 (accept_3_2 10 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 224 (Polychromatic418967fa.accept_25_8_23_24_1_13358 8 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 224 (accept_3_2 7 123 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 123 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 224 (accept_3_2 4 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 123 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 224 (accept_3_2 1 123 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 122 224 (Eq.refl Bool.true) (allA_succ_of_gcd 102 122 224 2 51 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 122 224 (Polychromatic418967fa.accept_9_2_5_8_1_11
  101 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 122 224 2 50 61 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 122 224
  (Polychromatic418967fa.accept_13_8_5_3_1_427 99 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 122 224 2 49 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 122 224 (accept_3_2 97 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 122 224 2 48 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 122 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 95 122 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 122 224 2 47 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 122 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 93 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 122 224 2 46 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 122 224 (accept_3_2 91 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 122 224 2 45 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 122 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 122 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 224 2 44 61 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 87 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 224 2 43 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 224 (accept_3_2 85 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 224 2 42 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 122 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 224 2 41 61 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 224
  (Polychromatic418967fa.accept_21_18_17_14_1_10491 81 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 122 224 2 40 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 122 224 (accept_3_2 79 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 224 2 39 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 77 122 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 224 2 38 61 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 75 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 224 2 37 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 224 (accept_3_2 73 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 224 2 36 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 122 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 224 2 35 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 224 2 34 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 224 (accept_3_2 67 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 224 2 33 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 122 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 224 2 32 61 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 224
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 224 2 31 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 224 (accept_3_2 61 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 224 2 30 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 122 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 224 2 29 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 224 2 28 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 224 (accept_3_2 55 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 224 2 27 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 122 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 224 2 26 61 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 224 2 25 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 224 (accept_3_2 49 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 224 2 24 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 122 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 224 2 23 61 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 224
  (Polychromatic418967fa.accept_13_6_5_3_1_426 45 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 224 2 22 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 224 (accept_3_2 43 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 224 2 21 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 224 (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 122 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 224 2 20 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 224 2 19 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 224 (accept_3_2 37 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 224 2 18 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 122 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 224 2 17 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 224 2 16 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 224 (accept_3_2 31 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 224 2 15 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 122 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 224 2 14 61 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 224 2 13 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 224 (accept_3_2 25 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 224 2 12 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 122 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 224 2 11 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 224 2 10 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 224 (accept_3_2 19 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 224 2 9 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 122 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 224 2 8 61 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 224 2 7 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 224 (accept_3_2 13 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 224 2 6 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 122 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 224 2 5 61 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 224
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 224 2 4 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 224 (accept_3_2 7 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  224 2 3 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 122 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 224 2 2 61 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 122 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 224 2 1 61 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 224 (accept_3_2 1 122 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 121 224 (Eq.refl Bool.true) (allA_of_3_0 104 121 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 120
  224 (Eq.refl Bool.true) (allA_succ_of_gcd 104 120 224 8 13 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120 224 (accept_3_2 103 120 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 120 224 2 51 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 120 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 120 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 120 224 4 25 30 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 120 224
  (Polychromatic418967fa.accept_19_4_6_15_1_7916 99 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 120 224 2 49 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 120 224 (accept_3_2 97 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 120 224 8 12 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 120 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 120 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 120 224 2 47 60 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 120 224
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 93 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 120 224 4 23 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 120 224 (accept_3_2 91 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 224 2 45 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 120 224 (Polychromatic418967fa.accept_19_13_6_15_1_9287 89 120 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 120 224 8 11 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 120 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 87 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 120 224 2 43 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 120 224 (accept_3_2 85 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 224 4 21 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 120 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 224 2 41 60 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 120 224
  (Polychromatic418967fa.accept_19_5_6_15_1_10686 81 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 120 224 8 10 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 120 224 (accept_3_2 79 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 224 2 39 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 120 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 224 4 19 30 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 120 224
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 75 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 120 224 2 37 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 120 224 (accept_3_2 73 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 224 8 9 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 120 224 (Polychromatic418967fa.accept_11_5_10_4_1_1157 71 120 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 224 2 35 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 120 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 69
  120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 120 224 4 17 30 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 224 (accept_3_2 67
  120 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 120 224 2 33 60 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 120 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 120 224 8 8 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 120 224 (Polychromatic418967fa.accept_25_13_20_24_1_13357 63 120 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 120 224 2 31 60 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 224 (accept_3_2 61 120 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 120 224 4 15 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 120 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 59
  120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 224 2 29 60 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 224
  (Polychromatic418967fa.accept_17_6_1_3_1_8503 57 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 120 224 8 7 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 120 224 (accept_3_2 55 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  120 224 2 27 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 120 224 (Polychromatic418967fa.accept_17_2_1_3_1_2357 53 120 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 224 4 13 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 51
  120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 224 2 25 60 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 224 (accept_3_2 49
  120 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 224 8 6 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 120 224 2 23 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 120 224 (Polychromatic418967fa.accept_21_3_15_14_1_5722 45 120 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 120 224 4 11 30 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 224 (accept_3_2 43 120 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 224 2 21 60 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 224 8 5 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 120 224 (Polychromatic418967fa.accept_18_3_12_8_1_5415 39 120 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 224 2 19 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 224 (accept_3_2 37 120 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 224 4 9 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 120 224 (Polychromatic418967fa.accept_19_16_6_15_1_2441 35 120
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 224 2 17 60 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 120 224 8 4 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 120 224 (accept_3_2 31 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  120 224 2 15 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 120 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 224 4 7 30 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 224 (Polychromatic418967fa.accept_11_5_10_4_1_1157
  27 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 224 2 13 60 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 224
  (accept_3_2 25 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 224 8 3 15 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 224 2 11 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 120 224 (Polychromatic418967fa.accept_18_3_12_8_1_5415 21 120 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 224 4 5 30 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 224 (accept_3_2 19 120 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 224 2 9 60 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 224
  (Polychromatic418967fa.accept_21_17_15_14_1_5707 17 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 120 224 8 2 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 120 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 120 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 224 2 7 60 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 224 (accept_3_2 13 120 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 224 4 3 30 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 224 2 5 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 120 224 (Polychromatic418967fa.accept_17_9_1_3_1_4626 9 120 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 224 8 1 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 224 (accept_3_2 7 120 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 224 2 3 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 120 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 224 4 1 30 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 224
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 3 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 120 224 2 1 60 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 120 224 (accept_3_2 1 120 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 119 224 (Eq.refl Bool.true) (allA_succ_of_gcd 105 119 224 7 15 17 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 119 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 104 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 119 224 (accept_3_2 103 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 119 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 119 224 (Polychromatic418967fa.accept_11_2_9_4_1_310 101 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 224 (accept_3_2 100 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 119 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 119 224 7 14 17 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 119 224 (accept_3_2 97
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 119 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 96 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 119 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 224 (accept_3_2 94 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 119 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 119 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 224 (Polychromatic418967fa.accept_13_1_2_3_1_911
  92 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 119 224 7 13 17 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 119 224
  (Polychromatic418967fa.accept_11_2_9_4_1_310 90 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 119 224 (Polychromatic418967fa.accept_13_11_2_3_1_883 89 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 224 (accept_3_2 88 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 119 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 119 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 224 (Polychromatic418967fa.accept_9_5_2_8_1_109
  86 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 119 224 (accept_3_2 85
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 119 224 7 12 17 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 119 224
  (Polychromatic418967fa.accept_10_3_9_4_1_960 83 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 119 224 (accept_3_2 82 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 119 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 119 224 (Polychromatic418967fa.accept_19_4_5_15_1_2437 80 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 119 224 (accept_3_2 79 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 119 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 119 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 119 224 7 11 17 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 119 224 (accept_3_2 76
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 75 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 119 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 224 (accept_3_2 73 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 119 224 (Polychromatic418967fa.accept_22_6_9_4_1_13356 72 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 224
  (Polychromatic418967fa.accept_22_5_9_4_1_10289 71 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 119 224 7 10 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 119 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 119 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 224 (Polychromatic418967fa.accept_9_5_2_8_1_109
  68 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 224 (accept_3_2 67
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 119 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 66 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 119 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 65 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 224 (accept_3_2 64 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 119 224 7 9 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 119 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 224 (accept_3_2 61 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 119 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 224 (accept_3_2 58 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 119 224 7 8 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 119 224 (accept_3_2 55 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 119 224 (Polychromatic418967fa.accept_20_14_19_4_1_7534 54 119 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 224 (Polychromatic418967fa.accept_10_3_9_4_1_960
  53 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 224 (accept_3_2 52
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 119 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 119 224 7 7 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 119 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 48
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 224
  (Polychromatic418967fa.accept_19_9_5_15_1_2544 47 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 224 (accept_3_2 46 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 224 (Polychromatic418967fa.accept_13_5_2_3_1_1526 44 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 224 (accept_3_2 43 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 119 224 7 6 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 119 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 41
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 224 (accept_3_2 40
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 119 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 224 (accept_3_2 37 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 119 224 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 119 224 7 5 17 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 119 224 (accept_3_2 34 119 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 224 (accept_3_2 31 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 224 (Polychromatic418967fa.accept_19_10_5_15_1_6443 29 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 119 224 7 4 17 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 119 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 119 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 224 (accept_3_2 25 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 119 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 119 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 224 (Polychromatic418967fa.accept_9_5_2_8_1_109
  23 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 224 (accept_3_2 22
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 119 224 7 3 17 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 119 224
  (Polychromatic418967fa.accept_19_1_5_15_1_3722 20 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 224 (accept_3_2 19 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 224 (Polychromatic418967fa.accept_19_17_5_15_1_7921 17 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 224 (accept_3_2 16 119 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 119 224 7 2 17 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 119 224 (accept_3_2 13
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 119 224 (Polychromatic418967fa.accept_13_11_2_3_1_883 11 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 224 (accept_3_2 10 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 119 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 8
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 119 224 7 1 17 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 119 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 6 119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 119 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 224 (accept_3_2 4 119 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 119 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 224 (Polychromatic418967fa.accept_11_2_9_4_1_310 2
  119 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 224 (accept_3_2 1 119
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 118 224 (Eq.refl Bool.true) (allA_of_3_0 107 118 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 108 117 224 (Eq.refl Bool.true) (allA_succ_of_accept 107 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 224 (accept_3_2 106 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 117 224 (Polychromatic418967fa.accept_19_10_3_15_1_13355 105 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 224 (Polychromatic418967fa.accept_19_9_3_15_1_2429 104 117 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 224 (accept_3_2 103 117 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 224 (Polychromatic418967fa.accept_10_2_7_4_1_967
  102 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 117 224 (accept_3_2 100 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 117 224 (Polychromatic418967fa.accept_15_9_12_14_1_963 99 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 117 224 (Polychromatic418967fa.accept_22_10_7_4_1_7008 98 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 224 (accept_3_2 97 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 224 (Polychromatic418967fa.accept_11_8_7_4_1_3011 96 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 224 (accept_3_2 94 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 117 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 93 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 117 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 92 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 224 (accept_3_2 91 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 224 (accept_3_2 88 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 117 224 (Polychromatic418967fa.accept_20_7_17_4_1_3239 87 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 117 224 (Polychromatic418967fa.accept_15_11_12_14_1_2612 86 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 224 (accept_3_2 85 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 224 (Polychromatic418967fa.accept_15_9_12_14_1_963 84 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 117 224 (accept_3_2 82 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 117 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 81 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 117 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 80 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 224 (accept_3_2 79 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 224 (accept_3_2 76 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 117 224 (Polychromatic418967fa.accept_18_3_9_8_1_2977 75 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 117 224 (Polychromatic418967fa.accept_11_8_7_4_1_3011 74 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 224 (accept_3_2 73 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 224 (accept_3_2 70 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 117 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 69 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 224 (Polychromatic418967fa.accept_21_5_12_14_1_7241 68 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 224 (accept_3_2 67 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 224 (accept_3_2 64 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 117 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 63 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 62 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 224 (accept_3_2 61 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 224 (Polychromatic418967fa.accept_18_6_9_8_1_6812 60 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 224 (accept_3_2 58 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 117 224 (Polychromatic418967fa.accept_18_3_9_8_1_2977 57 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 117 224 (Polychromatic418967fa.accept_15_11_12_14_1_2612 56 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 224 (accept_3_2 55 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 224 (accept_3_2 52 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 117 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 51 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 224 (Polychromatic418967fa.accept_19_12_3_15_1_9234 50 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 224 (accept_3_2 49 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 224 (Polychromatic418967fa.accept_17_14_15_3_1_4618 48 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 224 (accept_3_2 46 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 224 (Polychromatic418967fa.accept_19_7_3_15_1_2428 45 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 224 (Polychromatic418967fa.accept_21_2_12_14_1_13354 44 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 224 (accept_3_2 43 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 224 (accept_3_2 40 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 224 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 224 (Polychromatic418967fa.accept_23_15_2_17_1_13353 38 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 224 (accept_3_2 37 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 224 (accept_3_2 34 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 224 (accept_3_2 31 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 224 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 224 (accept_3_2 28 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 224 (Polychromatic418967fa.accept_19_8_3_15_1_2510 27 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 224 (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 224 (accept_3_2 25 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 224 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 224 (accept_3_2 22 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 224 (Polychromatic418967fa.accept_23_20_2_17_1_13352 20 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 224 (accept_3_2 19 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 224 (accept_3_2 16 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 224 (Polychromatic418967fa.accept_21_15_12_14_1_7232 15 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 224 (accept_3_2 13 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 117
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 224 (accept_3_2 10 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 224 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 224 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 117 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 224 (accept_3_2 7 117 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 117 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 224 (accept_3_2 4 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 117 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 117 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 224 (accept_3_2 1 117 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 116 224 (Eq.refl Bool.true) (allA_succ_of_gcd 108 116 224 4 27 29 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 116 224
  (Polychromatic418967fa.accept_21_2_11_14_1_11805 107 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 116 224 2 53 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 105 116 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 105 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 116 224 4 26 29 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 116 224 (accept_3_2 103 116 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 116 224 2 51 58 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 116 224
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 101 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 116 224 4 25 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 116 224 (Polychromatic418967fa.accept_22_11_6_4_1_5345 99 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 116 224 2 49 58 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 116 224 (accept_3_2 97 116 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 116 224 4 24 29 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 116 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 95 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 116 224 2 47 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 116 224 (Polychromatic418967fa.accept_13_2_12_3_1_415 93 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 116 224 4 23 29 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 116 224 (accept_3_2 91 116 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 116 224 2 45 58 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 116 224
  (Polychromatic418967fa.accept_19_13_2_15_1_7920 89 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 116 224 4 22 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 116 224 (Polychromatic418967fa.accept_13_9_12_3_1_907 87 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 116 224 2 43 58 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 116 224 (accept_3_2 85 116 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 116 224 4 21 29 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 116 224
  (Polychromatic418967fa.accept_17_15_14_3_1_5947 83 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 116 224 2 41 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 116 224 (Polychromatic418967fa.accept_21_18_11_14_1_8846 81 116 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 116 224 4 20 29 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 116 224 (accept_3_2 79
  116 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 116 224 2 39 58 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 116 224
  (Polychromatic418967fa.accept_19_1_2_15_1_3684 77 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 116 224 4 19 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 116 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 75 116 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 116 224 2 37 58 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 116 224 (accept_3_2 73 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 116 224 4 18 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 116 224
  (Polychromatic418967fa.accept_21_8_11_14_1_5665 71 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 116 224 2 35 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 116 224 (Polychromatic418967fa.accept_13_4_12_3_1_2999 69 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 116 224 4 17 29 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 116 224 (accept_3_2 67 116 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 116 224 2 33 58 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 116 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 65 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 116 224 4 16 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 116 224 (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 116 224 2 31 58 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 116 224 (accept_3_2 61 116 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 116 224 4 15 29 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 116 224
  (Polychromatic418967fa.accept_25_9_16_24_1_13351 59 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 116 224 2 29 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 116 224 (Polychromatic418967fa.accept_11_2_6_4_1_3028 57 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 116 224 4 14 29 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 116 224 (accept_3_2 55 116 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 116 224 2 27 58 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 116 224
  (Polychromatic418967fa.accept_17_2_14_3_1_4679 53 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 116 224 4 13 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 116 224 (Polychromatic418967fa.accept_19_13_2_15_1_7920 51 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 116 224 2 25 58 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 116 224 (accept_3_2 49 116 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 116 224 4 12 29 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 116 224
  (Polychromatic418967fa.accept_19_9_2_15_1_6432 47 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 116 224 2 23 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 116 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 116 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 116 224 4 11 29 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 116 224 (accept_3_2 43 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 116 224 2 21 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 116 224 (Polychromatic418967fa.accept_13_2_12_3_1_415
  41 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 224 4 10 29 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 224
  (Polychromatic418967fa.accept_19_1_2_15_1_3684 39 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 224 2 19 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 224 (accept_3_2 37 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 224 4 9 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 116 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 224 2 17 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 224
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 33 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 116 224 4 8 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 116 224 (accept_3_2 31 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 224 2 15 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 224 (Polychromatic418967fa.accept_21_8_11_14_1_5665 29 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 224 4 7 29 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 224
  (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 116 224 2 13 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 116 224 (accept_3_2 25 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 224 4 6 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 116 224 (Polychromatic418967fa.accept_17_6_14_3_1_4678 23 116 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 224 2 11 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 224
  (Polychromatic418967fa.accept_24_21_20_8_1_13350 21 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 116 224 4 5 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 116 224 (accept_3_2 19 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 224 2 9 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 116 224 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 224 4 4 29 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 116 224 2 7 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 116 224 (accept_3_2 13 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 116 224 4 3 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 116 224 (Polychromatic418967fa.accept_17_11_14_3_1_1427 11 116 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 116 224 2 5 58 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 224
  (Polychromatic418967fa.accept_13_9_12_3_1_907 9 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 116 224 4 2 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 116 224 (accept_3_2 7 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116
  224 2 3 58 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  116 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 116 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 116 224 4 1 29 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 116 224 (Polychromatic418967fa.accept_15_3_11_14_1_1705 3 116 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 224 2 1 58 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 224 (accept_3_2 1 116 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 115 224 (Eq.refl Bool.true) (allA_of_3_0 110 115 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 111 114 224 (Eq.refl Bool.true) (allA_succ_of_gcd 110 114 224 2 55 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 224 (accept_3_2 109 114 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 114 224 2 54 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 114 224
  (Polychromatic418967fa.accept_21_2_9_14_1_4189 107 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 114 224 2 53 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 105 114 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 105 114 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 114 224 2 52 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 224 (accept_3_2 103 114 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 114 224 2 51 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 114 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 101 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 114 224 2 50 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 114 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 99 114 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 224 2 49 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 224 (accept_3_2 97 114 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 114 224 2 48 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 114 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 95
  114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 224 2 47 57 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 114 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 93 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 114 224 2 46 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 114 224 (accept_3_2 91 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 224 2 45 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 224 (Polychromatic418967fa.accept_13_11_10_3_1_3020 89 114 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 224 2 44 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 114 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 114 224 2 43 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 114 224 (accept_3_2 85 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 224 2 42 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 114 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 224 2 41 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 114 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 114 224 2 40 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 114 224 (accept_3_2 79 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 224 2 39 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 114 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 224 2 38 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 114 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 75 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 114 224 2 37 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 114 224 (accept_3_2 73 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 224 2 36 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 224 (Polychromatic418967fa.accept_13_6_10_3_1_897 71 114 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 224 2 35 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 114 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 114 224 2 34 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 114 224 (accept_3_2 67 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 224 2 33 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 114 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 224 2 32 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 114 224 2 31 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 224 (accept_3_2 61 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 224 2 30 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 114 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 224 2 29 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 224 2 28 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 224 (accept_3_2 55 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 224 2 27 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 224 (Polychromatic418967fa.accept_15_8_9_14_1_4577 53 114 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 224 2 26 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 224 2 25 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 224 (accept_3_2 49 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 224 2 24 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 114 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 224 2 23 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 224 2 22 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 224 (accept_3_2 43 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 224 2 21 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 114 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 224 2 20 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 224 2 19 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 224 (accept_3_2 37 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 224 2 18 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 224 (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 114 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 224 2 17 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 224 2 16 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 224 (accept_3_2 31 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 224 2 15 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 114 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 224 2 14 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 224 2 13 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 224 (accept_3_2 25 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 224 2 12 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 114 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 224 2 11 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 224 2 10 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 224 (accept_3_2 19 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 224 2 9 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 224 (Polychromatic418967fa.accept_21_17_9_14_1_5700 17 114 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 224 2 8 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 114 224 2 7 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 114 224 (accept_3_2 13 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 224 2 6 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 114 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 224 2 5 57 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 224 2 4 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 224 (accept_3_2 7 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114
  224 2 3 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  114 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 114 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 224 2 2 57 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 114 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 114 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 224 2 1 57 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 224 (accept_3_2 1 114 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 113 224 (Eq.refl Bool.true) (allA_succ_of_accept 111 113 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 111 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 113 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 113 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 224 (accept_3_2 109 113 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 113 224 (Polychromatic418967fa.accept_21_3_8_14_1_8864 108 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 113 224
  (Polychromatic418967fa.accept_10_7_3_4_1_978 107 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 113 224 (accept_3_2 106 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 113 224 (Polychromatic418967fa.accept_17_2_11_3_1_4654 104 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 113 224 (accept_3_2 103 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 113 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 113
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 113 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 101 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 113 224 (accept_3_2 100 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 113 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 98 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 113 224 (accept_3_2 97 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 113 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 113 224
  (Polychromatic418967fa.accept_11_7_3_4_1_729 95 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 113 224 (accept_3_2 94 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 113 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 113 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 113 224 (accept_3_2 91 113 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 113 224 (Polychromatic418967fa.accept_13_12_9_3_1_3047 90 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 113 224
  (Polychromatic418967fa.accept_10_9_3_4_1_985 89 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 113 224 (accept_3_2 88 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 113 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 86 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 113 224 (accept_3_2 85 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 113 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 113 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 113 224 (accept_3_2 82 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 113 224 (Polychromatic418967fa.accept_13_2_9_3_1_2212 80 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 113 224 (accept_3_2 79 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 113 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 113 224
  (Polychromatic418967fa.accept_10_7_3_4_1_978 77 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 113 224 (accept_3_2 76 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 113 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 113 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 113 224 (accept_3_2 73 113 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 113 224 (Polychromatic418967fa.accept_13_7_9_3_1_1504 72 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 224
  (Polychromatic418967fa.accept_13_6_9_3_1_915 71 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 113 224 (accept_3_2 70 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 113 224 (Polychromatic418967fa.accept_18_14_5_8_1_1880 68 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 224 (accept_3_2 67 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 113 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 113 224 (accept_3_2 64 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 113 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 62 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 224 (accept_3_2 61 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 224
  (Polychromatic418967fa.accept_10_9_3_4_1_985 59 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 224 (accept_3_2 58 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 113 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 224 (accept_3_2 55 113 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 224 (Polychromatic418967fa.accept_13_2_9_3_1_2212 54 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 224
  (Polychromatic418967fa.accept_17_2_11_3_1_4654 53 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 224 (accept_3_2 52 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 224 (accept_3_2 49 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 224 (accept_3_2 46 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 224 (Polychromatic418967fa.accept_13_5_9_3_1_870 44 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 224 (accept_3_2 43 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 224
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 41 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 224 (accept_3_2 40 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 113 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 224 (accept_3_2 37 113 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 224 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 224
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 224 (accept_3_2 34 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 224 (Polychromatic418967fa.accept_13_6_9_3_1_915 32 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 224 (accept_3_2 31 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 224 (accept_3_2 28 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 224 (accept_3_2 25 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 224
  (Polychromatic418967fa.accept_19_4_18_15_1_7899 23 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 113 224 (accept_3_2 22 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 224 (accept_3_2 19 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 224 (Polychromatic418967fa.accept_11_7_3_4_1_729
  18 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 224
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 224 (accept_3_2 16 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 224 (accept_3_2 13 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 113 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 224 (accept_3_2 10 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 224 (Polychromatic418967fa.accept_13_8_9_3_1_2213 8 113 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 224 (accept_3_2 7 113 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 113 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 224
  (Polychromatic418967fa.accept_13_5_9_3_1_870 5 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 224 (accept_3_2 4 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 113 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 224 (accept_3_2 1 113 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 224 (allA_of_3_0 112 112 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 224
  (allA_succ_of_accept 110 111 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 110 111 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 224 (accept_3_2 109 111 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 224 (Polychromatic418967fa.accept_13_4_7_3_1_92 108 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 224 (accept_3_2 106 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 104 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 224 (accept_3_2 103 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 102 111
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 224 (accept_3_2 100 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 224 (Polychromatic418967fa.accept_13_8_7_3_1_430 99 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 224 (Polychromatic418967fa.accept_15_8_6_14_1_975 98 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 224 (accept_3_2 97 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 111 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 224 (accept_3_2 94 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 224 (Polychromatic418967fa.accept_20_13_11_4_1_2042 93 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 92 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 224 (accept_3_2 91 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 224 (accept_3_2 88 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 86 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 224 (accept_3_2 85 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 224 (Polychromatic418967fa.accept_15_9_6_14_1_2627 84 111 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 224 (accept_3_2 82 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 224 (Polychromatic418967fa.accept_18_9_3_8_1_5419 81 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 224 (Polychromatic418967fa.accept_15_5_6_14_1_1721 80 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 224 (accept_3_2 79 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 111 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 224 (accept_3_2 76 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 75 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 224 (accept_3_2 73 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 224 (Polychromatic418967fa.accept_21_9_6_14_1_7228 72 111 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 224 (accept_3_2 70 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 224 (accept_3_2 67 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 224 (accept_3_2 64 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 224 (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 224 (Polychromatic418967fa.accept_13_10_7_3_1_3041 62 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 224 (accept_3_2 61 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 111 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 224 (accept_3_2 58 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447 57 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 224 (accept_3_2 55 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 224 (accept_3_2 52 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 224 (accept_3_2 49 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 224 (Polychromatic418967fa.accept_13_9_7_3_1_1531 48 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 224 (accept_3_2 46 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 224 (Polychromatic418967fa.accept_17_10_9_3_1_7144 44 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 224 (accept_3_2 43 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 111 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 224 (accept_3_2 40 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 224 (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 224 (accept_3_2 37 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 224 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 111 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 224 (accept_3_2 34 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 224 (accept_3_2 31 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 224 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 224 (accept_3_2 28 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 224 (Polychromatic418967fa.accept_24_2_15_8_1_6377 26 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 224 (accept_3_2 25 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 111 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 224 (accept_3_2 22 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 224 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 224 (accept_3_2 19 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 224 (accept_3_2 16 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 224 (accept_3_2 13 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 224 (Polychromatic418967fa.accept_18_12_3_8_1_6817 12 111 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 224 (accept_3_2 10 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 224 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 224 (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 224 (accept_3_2 7 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 111 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 224 (accept_3_2 4 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 224 (Polychromatic418967fa.accept_19_3_16_15_1_9281 3 111 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 224 (accept_3_2 1 111 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 224 (allA_succ_of_accept 109 110 224 (accept_3_2 109 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 110 224 2 54 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 110 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 107 110 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 110 224 2 53 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 110 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 105 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 110 224 2 52 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 110 224 (accept_3_2 103 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 110 224 2 51 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 110 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 101 110 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 224 2 50 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 224
  (Polychromatic418967fa.accept_15_9_5_14_1_973 99 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 110 224 2 49 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 110 224 (accept_3_2 97 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 110 224 2 48 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 110 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 110 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 110 224 2 47 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 93 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 110 224 2 46 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 110 224 (accept_3_2 91 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 224 2 45 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 110 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 224 2 44 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 87 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 224 2 43 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 110 224 (accept_3_2 85 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 110 224 2 42 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 110 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 110 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 224 2 41 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 224
  (Polychromatic418967fa.accept_15_6_5_14_1_429 81 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 224 2 40 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 224 (accept_3_2 79 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 224 2 39 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 110 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 224 2 38 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 110 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 110 224 2 37 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 110 224 (accept_3_2 73 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 110 224 2 36 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 110 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 110 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 224 2 35 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 69 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 110 224 2 34 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 110 224 (accept_3_2 67 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 224 2 33 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 110 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 110 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 224 2 32 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 224
  (Polychromatic418967fa.accept_17_12_8_3_1_4646 63 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 224 2 31 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 224 (accept_3_2 61 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 224 2 30 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 110 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 224 2 29 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 224 2 28 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 224 (accept_3_2 55 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 224 2 27 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 110 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 224 2 26 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 224 2 25 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 224 (accept_3_2 49 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 224 2 24 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 110 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 224 2 23 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 224
  (Polychromatic418967fa.accept_20_5_10_4_1_4548 45 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 224 2 22 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 110 224 (accept_3_2 43 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 224 2 21 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 110 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 224 2 20 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 224 2 19 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 224 (accept_3_2 37 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 224 2 18 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 110 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 224 2 17 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 224 2 16 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 224 (accept_3_2 31 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 224 2 15 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 110 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 224 2 14 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 224
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 224 2 13 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 224 (accept_3_2 25 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 224 2 12 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 110 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 224 2 11 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 224 2 10 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 224 (accept_3_2 19 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 224 2 9 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 110 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 224 2 8 55 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 110 224 2 7 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 110 224 (accept_3_2 13 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 110 224 2 6 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 110 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 110 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 224 2 5 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 224
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 224 2 4 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 224 (accept_3_2 7 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  224 2 3 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 110 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 224 2 2 55 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 110 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 110 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 224 2 1 55 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 224 (accept_3_2 1 110 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 224 (allA_of_3_0 109 109 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 224
  (allA_succ_of_accept 107 108 224 (Polychromatic418967fa.accept_15_2_3_14_1_972 107 108 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 108 224 2 53 54 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 108 224
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 105 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 108 224 4 26 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 108 224 (accept_3_2 103 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 224 2 51 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 224 (Polychromatic418967fa.accept_11_2_9_4_1_310 101 108 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 108 224 4 25 27 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 108 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 99 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 108 224 2 49 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 108 224 (accept_3_2 97 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 224 4 24 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 224 (Polychromatic418967fa.accept_21_11_3_14_1_13349 95 108 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 108 224 2 47 54 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 108 224
  (Polychromatic418967fa.accept_19_17_13_15_1_1402 93 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 108 224 4 23 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 108 224 (accept_3_2 91 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 224 2 45 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 108 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 89 108 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 224 4 22 27 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 108 224
  (Polychromatic418967fa.accept_22_21_20_4_1_6989 87 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 108 224 2 43 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 108 224 (accept_3_2 85 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 224 4 21 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 224 (Polychromatic418967fa.accept_19_7_13_15_1_2407 83 108 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 224 2 41 54 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 108 224
  (Polychromatic418967fa.accept_22_15_20_4_1_10168 81 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 108 224 4 20 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 108 224 (accept_3_2 79 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 224 2 39 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 224 (Polychromatic418967fa.accept_13_12_4_3_1_1528 77 108 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 224 4 19 27 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 108 224
  (Polychromatic418967fa.accept_21_12_3_14_1_10498 75 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 108 224 2 37 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 108 224 (accept_3_2 73 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 224 4 18 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 224 (Polychromatic418967fa.accept_15_11_3_14_1_971 71 108 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 224 2 35 54 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 108 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 69 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 108 224 4 17 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 108 224 (accept_3_2 67 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 224 2 33 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 224 (Polychromatic418967fa.accept_17_14_6_3_1_2362 65 108 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 224 4 16 27 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 108 224
  (Polychromatic418967fa.accept_19_6_13_15_1_2406 63 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 108 224 2 31 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 108 224 (accept_3_2 61 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 224 4 15 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 108 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 224 2 29 54 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 108 224
  (Polychromatic418967fa.accept_11_2_9_4_1_310 57 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 108 224 4 14 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 224 (accept_3_2 55 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 224 2 27 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 224 (Polychromatic418967fa.accept_13_1_4_3_1_1545 53 108 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 224 4 13 27 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 224
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 51 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 108 224 2 25 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 224 (accept_3_2 49 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 224 4 12 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 224 (Polychromatic418967fa.accept_15_2_3_14_1_972 47 108 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 224 2 23 54 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 224
  (Polychromatic418967fa.accept_19_7_13_15_1_2407 45 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 108 224 4 11 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 108 224 (accept_3_2 43 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 224 2 21 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 224 (Polychromatic418967fa.accept_15_11_3_14_1_971 41 108 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 224 4 10 27 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 224 2 19 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 224 (accept_3_2 37 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 224 4 9 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 224 (Polychromatic418967fa.accept_11_2_9_4_1_310 35 108 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 224 2 17 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 224 (Polychromatic418967fa.accept_13_7_4_3_1_3064
  33 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 224 4 8 27 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 224
  (accept_3_2 31 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 224 2 15 54 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 29 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 224 4 7 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 108 224 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 108 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 224 2 13 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 224 (accept_3_2 25 108 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 224 4 6 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 224 (Polychromatic418967fa.accept_19_4_13_15_1_3676 23 108
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 224 2 11 54 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 224
  (Polychromatic418967fa.accept_19_2_13_15_1_9274 21 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 108 224 4 5 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 108 224 (accept_3_2 19 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 224 2 9 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 108 224 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 108 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 224 4 4 27 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 224
  (Polychromatic418967fa.accept_21_15_3_14_1_4141 15 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 108 224 2 7 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 224 (accept_3_2 13 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 224 4 3 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 224 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 108 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 224 2 5 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 9
  108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 224 4 2 27 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 224 (accept_3_2 7
  108 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 224 2 3 54 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 224
  (Polychromatic418967fa.accept_17_5_6_3_1_4640 5 108 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 224 4 1 27 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 108 224 (Polychromatic418967fa.accept_26_3_4_16_1_13348 3 108 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 224 2 1 54 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 224 (accept_3_2 1 108 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 224 (allA_succ_of_accept 106 107 224 (accept_3_2 106 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 224 (Polychromatic418967fa.accept_17_2_5_3_1_1416 104 107
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 224 (accept_3_2 103 107
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 102 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 101 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 224 (accept_3_2 100 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 107 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 224 (Polychromatic418967fa.accept_12_2_11_8_1_504
  98 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 107 224 (accept_3_2 97
  107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 107 224
  (Polychromatic418967fa.accept_21_12_2_14_1_10513 96 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 95 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 224 (accept_3_2 94 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 107 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 92 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 224 (accept_3_2 91 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 224 (Polychromatic418967fa.accept_21_6_2_14_1_5688 90 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 224 (Polychromatic418967fa.accept_11_1_8_4_1_717 89 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 224 (accept_3_2 88 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 107 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 86 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 224 (accept_3_2 85 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 84 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 83 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 224 (accept_3_2 82 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 107 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 224
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 80 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 224 (accept_3_2 79 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 224 (Polychromatic418967fa.accept_11_1_8_4_1_717 78 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 224 (Polychromatic418967fa.accept_18_5_17_8_1_2984 77 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 224 (accept_3_2 76 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 107 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 74 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 224 (accept_3_2 73 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 71 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 224 (accept_3_2 70 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 107 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 224
  (Polychromatic418967fa.accept_27_14_26_8_1_13347 68 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 107 224 (accept_3_2 67 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 107 224 (Polychromatic418967fa.accept_21_3_2_14_1_7235 66 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 224 (Polychromatic418967fa.accept_15_5_2_14_1_1693 65 107
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 224 (accept_3_2 64 107
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 107 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 62 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 224 (accept_3_2 61 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 107 224 (Polychromatic418967fa.accept_19_3_12_15_1_568 60 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 224
  (Polychromatic418967fa.accept_17_8_5_3_1_2397 59 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 224 (accept_3_2 58 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 224 (Polychromatic418967fa.accept_11_1_8_4_1_717 56 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 224 (accept_3_2 55 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 224 (Polychromatic418967fa.accept_19_16_12_15_1_6449 54
  107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 224
  (Polychromatic418967fa.accept_10_3_7_4_1_584 53 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 224 (accept_3_2 52 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 224 (accept_3_2 49 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 224 (Polychromatic418967fa.accept_15_3_2_14_1_1713 48 107
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 224
  (Polychromatic418967fa.accept_22_3_19_4_1_13346 47 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 107 224 (accept_3_2 46 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 224 (Polychromatic418967fa.accept_19_6_12_15_1_7895 44 107
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 224 (accept_3_2 43 107
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 42 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 107 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 41 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 224 (accept_3_2 40 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 224 (Polychromatic418967fa.accept_12_2_11_8_1_504
  38 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 224 (accept_3_2 37
  107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 224
  (Polychromatic418967fa.accept_17_2_5_3_1_1416 36 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 107 224 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 224 (accept_3_2 34 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 107 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 224 (Polychromatic418967fa.accept_10_2_7_4_1_967
  32 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 224 (accept_3_2 31
  107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 224
  (Polychromatic418967fa.accept_21_9_2_14_1_7251 30 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 107 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 29 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 224 (accept_3_2 28 107 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 224 (Polychromatic418967fa.accept_12_2_11_8_1_504
  26 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 224 (accept_3_2 25
  107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 224
  (Polychromatic418967fa.accept_19_5_12_15_1_9244 24 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 224 (accept_3_2 22 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 224
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 224 (accept_3_2 19 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 224 (Polychromatic418967fa.accept_19_17_12_15_1_11981 17 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 224 (accept_3_2 16 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 224 (accept_3_2 13 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 224 (accept_3_2 10 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 224
  (Polychromatic418967fa.accept_17_8_5_3_1_2397 8 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 224 (accept_3_2 7 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 224 (Polychromatic418967fa.accept_17_6_5_3_1_7134 6 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 224 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 224 (accept_3_2 4 107 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 224 (accept_3_2 1 107 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 224 (allA_of_3_0 106 106 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 224
  (allA_succ_of_accept 104 105 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 104 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 224 (accept_3_2 103 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 105 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 224 (accept_3_2 100 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 99 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 105 224 7 14 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 105 224 (accept_3_2 97 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 105 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 96 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 105 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 105 224 (accept_3_2 94 105 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 105 224 (Polychromatic418967fa.accept_9_3_6_8_1_308
  93 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 105 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 92 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 91 105 224 7 13 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 90 105 224 (Polychromatic418967fa.accept_11_2_6_4_1_3028 90 105 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 224 (accept_3_2 88 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 224 (Polychromatic418967fa.accept_19_11_10_15_1_3741 87 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 86 105 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 224 (accept_3_2 85 105 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 105 224 7 12 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 105 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 224 (accept_3_2 82
  105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 105 224
  (Polychromatic418967fa.accept_10_1_5_4_1_276 81 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 105 224 (Polychromatic418967fa.accept_13_2_1_3_1_419 80 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 224 (accept_3_2 79 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 105 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 105 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 105 224 7 11 15 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 105 224 (accept_3_2 76 105 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 105 224 (Polychromatic418967fa.accept_9_3_6_8_1_308
  75 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 105 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 105 224 (accept_3_2 73 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 105 224 (Polychromatic418967fa.accept_13_7_1_3_1_1523 72 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 105 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 105 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 224 7 10 15 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 105 224
  (Polychromatic418967fa.accept_10_9_5_4_1_966 69 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 105 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 224 (accept_3_2 67 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 105 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 105 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 65
  105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 224 (accept_3_2 64
  105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 105 224 7 9 15 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 105 224
  (Polychromatic418967fa.accept_19_5_10_15_1_5076 62 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 105 224 (accept_3_2 61 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 105 224 (Polychromatic418967fa.accept_19_3_10_15_1_9241 60 105 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 59
  105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 224 (accept_3_2 58
  105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 105 224 7 8 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 105 224 (accept_3_2 55 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 105 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 105 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 224 (accept_3_2 52 105 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 224 (Polychromatic418967fa.accept_10_1_5_4_1_276 51 105 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 105 224 7 7 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 105 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 105 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 224 (accept_3_2 46 105 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 224 (Polychromatic418967fa.accept_13_6_1_3_1_1522
  45 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 224
  (Polychromatic418967fa.accept_13_5_1_3_1_878 44 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 224 (accept_3_2 43 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  105 224 7 6 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 105 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 105 224 (accept_3_2 40 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 105 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 105 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 224 (accept_3_2 37 105 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 224 (Polychromatic418967fa.accept_10_6_5_4_1_571
  36 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 224 7 5 15 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 224
  (accept_3_2 34 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 224
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 33 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 105 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 224 (accept_3_2 31 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 105 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 105 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 105 224 7 4 15 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 105 224
  (Polychromatic418967fa.accept_22_5_17_4_1_10306 27 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 105 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 224 (accept_3_2 25 105 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 224 (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 105
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 224 (accept_3_2 22 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  105 224 7 3 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 105 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 105 224 (accept_3_2 19 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 224 (accept_3_2 16 105 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 224 (Polychromatic418967fa.accept_13_2_1_3_1_419
  15 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 105 224 7 2 15 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 105 224
  (accept_3_2 13 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 224 (accept_3_2 10 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 105 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 224
  (Polychromatic418967fa.accept_25_8_5_24_1_13345 8 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 105 224 7 1 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 105 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 105 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 224 (accept_3_2 4 105 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 224 (accept_3_2 1 105 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 224 (allA_succ_of_accept 103 104 224 (accept_3_2 103 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 224 2 51 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 104 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 224 4 25 26 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 224
  (Polychromatic418967fa.accept_17_14_2_3_1_7172 99 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 224 2 49 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 224 (accept_3_2 97 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 224 8 12 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 224 (Polychromatic418967fa.accept_18_5_14_8_1_2966 95 104 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 224 2 47 52 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 93 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 224 4 23 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 104 224 (accept_3_2 91 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 224 2 45 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 224 (Polychromatic418967fa.accept_19_13_9_15_1_11989 89 104 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 224 8 11 13 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 87 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 224 2 43 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 224 (accept_3_2 85 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 224 4 21 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 104 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 224 2 41 52 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 224
  (Polychromatic418967fa.accept_19_5_9_15_1_9239 81 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 224 8 10 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 224 (accept_3_2 79 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 224 2 39 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 224 (Polychromatic418967fa.accept_18_5_14_8_1_2966 77 104 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 224 4 19 26 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 75 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 224 2 37 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 224 (accept_3_2 73 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 224 8 9 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 104 224 (Polychromatic418967fa.accept_25_21_4_24_1_13344 71 104 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 224 2 35 52 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 224 4 17 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 224 (accept_3_2 67 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 224 2 33 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 104 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 224 8 8 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 224
  (Polychromatic418967fa.accept_19_6_9_15_1_3694 63 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 104 224 2 31 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 104 224 (accept_3_2 61 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 224 4 15 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 224 (Polychromatic418967fa.accept_18_5_14_8_1_2966 59 104 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 224 2 29 52 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 224 8 7 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 104 224 (accept_3_2 55 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  104 224 2 27 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 104 224 (Polychromatic418967fa.accept_21_11_20_14_1_4179 53 104 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 224 4 13 26 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 224 2 25 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 224 (accept_3_2 49 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 224 8 6 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 104 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 104 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 224 2 23 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 224 (Polychromatic418967fa.accept_17_11_2_3_1_8468
  45 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 104 224 4 11 26 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 104 224
  (accept_3_2 43 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 104 224 2 21 52 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 104 224
  (Polychromatic418967fa.accept_18_5_14_8_1_2966 41 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 104 224 8 5 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 104 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 104 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 104 224 2 19 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 104 224 (accept_3_2 37 104 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 104 224 4 9 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 104 224 (Polychromatic418967fa.accept_17_1_2_3_1_4668 35 104
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 224 2 17 52 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 224 8 4 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 104 224 (accept_3_2 31 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  104 224 2 15 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 104 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 104 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 224 4 7 26 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 224
  (Polychromatic418967fa.accept_21_6_20_14_1_8837 27 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 104 224 2 13 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 104 224 (accept_3_2 25 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 224 8 3 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 104 224 (Polychromatic418967fa.accept_18_5_14_8_1_2966 23 104 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 224 2 11 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 21
  104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 104 224 4 5 26 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 104 224 (accept_3_2 19
  104 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 104 224 2 9 52 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 104 224
  (Polychromatic418967fa.accept_21_17_20_14_1_11808 17 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 104 224 8 2 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 104 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 104 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 224 2 7 52 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 224 (accept_3_2 13 104 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 224 4 3 26 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 224 2 5 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 104 224 (Polychromatic418967fa.accept_21_9_20_14_1_4139 9 104 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 224 8 1 13 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 224 (accept_3_2 7 104 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104 224 2 3 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 104 224 (Polychromatic418967fa.accept_17_5_2_3_1_9775 5
  104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 224 4 1 26 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 104 224 2 1 52 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 104 224 (accept_3_2 1 104 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 224 (allA_of_3_0 103 103 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 224 (allA_succ_of_accept 101
  102 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 102 224 2 50 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 102 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 99 102 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 224 2 49 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 224 (accept_3_2 97 102 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 224 2 48 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 95 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 224 2 47 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 93 102 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 224 2 46 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 224 (accept_3_2 91 102 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 102 224 2 45 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 102 224
  (Polychromatic418967fa.accept_19_13_7_15_1_5054 89 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 102 224 2 44 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 102 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 102 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 102 224 2 43 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 224 (accept_3_2 85 102 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 102 224 2 42 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 102 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 102 224 2 41 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 102 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 81 102 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 102 224 2 40 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 224 (accept_3_2 79 102 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 102 224 2 39 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 102 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 77
  102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 224 2 38 51 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 102 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 102 224 2 37 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 102 224 (accept_3_2 73 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 224 2 36 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 224 (Polychromatic418967fa.accept_15_11_12_14_1_2612 71 102 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 224 2 35 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 69 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 224 2 34 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 102 224 (accept_3_2 67 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 224 2 33 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 102 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 224 2 32 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 102 224 2 31 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 224 (accept_3_2 61 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 224 2 30 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 102 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 224 2 29 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 224 2 28 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 224 (accept_3_2 55 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 224 2 27 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 224 (Polychromatic418967fa.accept_13_1_11_3_1_901 53 102 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 224 2 26 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 224 2 25 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 224 (accept_3_2 49 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 224 2 24 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 102 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 224 2 23 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 224 2 22 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 224 (accept_3_2 43 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 224 2 21 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 102 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 224 2 20 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 224 2 19 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 224 (accept_3_2 37 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 224 2 18 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 224 (Polychromatic418967fa.accept_20_15_2_4_1_11882 35 102 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 224 2 17 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 224 2 16 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 224 (accept_3_2 31 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 224 2 15 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 102 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 224 2 14 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 224 2 13 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 224 (accept_3_2 25 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 224 2 12 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 102 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 224 2 11 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 224 2 10 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 224 (accept_3_2 19 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 224 2 9 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 102 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 224 2 8 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 102 224 2 7 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 102 224 (accept_3_2 13 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 224 2 6 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 102 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 224 2 5 51 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 224 2 4 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 224 (accept_3_2 7 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102
  224 2 3 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  102 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 102 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 224 2 2 51 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 102 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 102 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 224 2 1 51 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 224 (accept_3_2 1 102 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 224 (allA_succ_of_accept 100 101 224 (accept_3_2 100 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 101 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 98 101
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 224 (accept_3_2 97 101
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 96 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 101 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 101 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 224 (accept_3_2 94 101 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 224
  (Polychromatic418967fa.accept_17_7_16_3_1_4660 92 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 101 224 (accept_3_2 91 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 101 224 (Polychromatic418967fa.accept_20_10_1_4_1_11933 90 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 101 224 (Polychromatic418967fa.accept_13_11_10_3_1_3020 89 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 224 (accept_3_2 88 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 101 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 224 (accept_3_2 85 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 83 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 224 (accept_3_2 82 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 101 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 224
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 80 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 224 (accept_3_2 79 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 224 (accept_3_2 76 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 74 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 101 224 (accept_3_2 73 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 101 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 72 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 224 (Polychromatic418967fa.accept_13_6_10_3_1_897 71 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 224 (accept_3_2 70 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 101 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 224 (accept_3_2 67 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 65 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 224 (accept_3_2 64 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 101 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 62 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 224 (accept_3_2 61 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 224 (accept_3_2 58 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 224
  (Polychromatic418967fa.accept_22_12_13_4_1_10363 56 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 101 224 (accept_3_2 55 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 101 224 (Polychromatic418967fa.accept_13_2_10_3_1_1538 54 101 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 224 (Polychromatic418967fa.accept_11_9_2_4_1_707 53 101
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 224 (accept_3_2 52 101
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 101 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 101 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 224 (accept_3_2 49 101 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 101 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447
  47 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 224 (accept_3_2 46
  101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 101 224 (Polychromatic418967fa.accept_21_2_17_14_1_5644 44 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 224 (accept_3_2 43 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 224 (accept_3_2 40 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 224 (accept_3_2 37 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 224 (Polychromatic418967fa.accept_21_15_17_14_1_4191 36
  101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 224
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 224 (accept_3_2 34 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 224 (accept_3_2 31 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 224
  (Polychromatic418967fa.accept_19_10_6_15_1_6444 29 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 101 224 (accept_3_2 28 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 101
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 224 (accept_3_2 25 101
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 101 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 101 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 224 (accept_3_2 22 101 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 224 (Polychromatic418967fa.accept_11_9_2_4_1_707
  20 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 224 (accept_3_2 19
  101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 224
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 224 (accept_3_2 16 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 224 (accept_3_2 13 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 224 (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 224 (accept_3_2 10 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 224
  (Polychromatic418967fa.accept_21_8_17_14_1_4156 8 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 224 (accept_3_2 7 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 224 (accept_3_2 4 101 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 224 (accept_3_2 1 101 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 224 (allA_of_3_0 100 100 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 224 (allA_succ_of_accept 98 99
  224 (Polychromatic418967fa.accept_10_8_9_4_1_961 98 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 99 224 (accept_3_2 97 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 99 224 (Polychromatic418967fa.accept_13_5_8_3_1_1535 96 99 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 99 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 224 (accept_3_2 94 99 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 224 (Polychromatic418967fa.accept_10_3_9_4_1_960
  93 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 224
  (Polychromatic418967fa.accept_21_8_15_14_1_4176 92 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 224 (accept_3_2 91 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 224 (accept_3_2 88 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 224 (Polychromatic418967fa.accept_13_9_8_3_1_3045 87 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 224
  (Polychromatic418967fa.accept_19_10_4_15_1_3720 86 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 224 (accept_3_2 85 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 224 (Polychromatic418967fa.accept_19_8_4_15_1_1414 84 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 224 (accept_3_2 82 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 81 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 224
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 80 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 224 (accept_3_2 79 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 78 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 224 (accept_3_2 76 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 75 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 224
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 74 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 224 (accept_3_2 73 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 224 (Polychromatic418967fa.accept_13_7_8_3_1_1533 72 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 224 (accept_3_2 70 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 224 (Polychromatic418967fa.accept_20_9_19_4_1_3202 69 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 224
  (Polychromatic418967fa.accept_10_8_9_4_1_961 68 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 224 (accept_3_2 67 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 224 (accept_3_2 64 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 224
  (Polychromatic418967fa.accept_17_11_14_3_1_1427 62 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 224 (accept_3_2 61 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 224 (Polychromatic418967fa.accept_18_6_9_8_1_6812 60 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 224 (accept_3_2 58 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 224 (Polychromatic418967fa.accept_13_5_8_3_1_1535 57 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 224
  (Polychromatic418967fa.accept_19_18_4_15_1_3721 56 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 224 (accept_3_2 55 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 224 (accept_3_2 52 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 51 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 224
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 50 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 224 (accept_3_2 49 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 224 (accept_3_2 46 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 224
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 44 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 224 (accept_3_2 43 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 224 (accept_3_2 40 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 224 (Polychromatic418967fa.accept_18_3_9_8_1_2977 39 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 224
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 224 (accept_3_2 37 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 224 (accept_3_2 34 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 224
  (Polychromatic418967fa.accept_17_15_14_3_1_5947 32 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 224 (accept_3_2 31 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 224 (accept_3_2 28 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 224 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 224
  (Polychromatic418967fa.accept_21_5_15_14_1_2787 26 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 224 (accept_3_2 25 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 224 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 224 (accept_3_2 22 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 224
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 224 (accept_3_2 19 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 224 (accept_3_2 16 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 224
  (Polychromatic418967fa.accept_19_14_4_15_1_2434 14 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 224 (accept_3_2 13 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 224 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 224 (accept_3_2 10 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 224 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 99 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 224
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 224 (accept_3_2 7 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  224 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 224 (accept_3_2 4 99 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 99 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 224 (Polychromatic418967fa.accept_17_2_14_3_1_4679
  2 99 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 224 (accept_3_2 1 99
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  224 (allA_succ_of_accept 97 98 224 (accept_3_2 97 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96
  98 224 2 48 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 95 98 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 224 2 47 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 224 (Polychromatic418967fa.accept_11_5_10_4_1_1157
  93 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 224 2 46 49 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 91 98 224 7 13 14 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 90 98 224 2 45 49
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 89 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 224 2 44 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 98 224 (Polychromatic418967fa.accept_13_9_7_3_1_1531 87 98 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 224 2 43 49 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 224 (accept_3_2 85 98 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 224 14 6 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 98 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 224 2 41 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 224
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 81 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 224 2 40 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 98 224 (accept_3_2 79 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 224 2 39 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 98 224 7 11 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 98 224 2 38 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 98 224 (Polychromatic418967fa.accept_13_10_7_3_1_3041 75 98 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 98 224 2 37 49 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 98 224 (accept_3_2 73 98 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 98 224 2 36 49 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 98 224
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 71 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 98 224 14 5 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 98 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 69 98 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 98 224 2 34 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 98 224 (accept_3_2 67 98 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 98 224 2 33 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 98 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 98 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 224 2 32 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 98 224 7 9 14 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 98 224 2 31 49 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 98 224
  (accept_3_2 61 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 98 224 2 30 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 98 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 59 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 98 224 2 29 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 98 224 (Polychromatic418967fa.accept_23_11_6_17_1_13343 57 98 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 224 14 4 7 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 224 (accept_3_2 55 98 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 98 224 2 27 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 98 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 53
  98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 224 2 26 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 224
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 51 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 224 2 25 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 98 224 7 7 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 98 224 2 24 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 98 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 98 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 224 2 23 49 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 224
  (Polychromatic418967fa.accept_19_7_3_15_1_2428 45 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 224 2 22 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 98 224 (accept_3_2 43 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 224 14 3 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 98 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 98 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 224 2 20 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 39
  98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 98 224 2 19 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 98 224 (accept_3_2 37
  98 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98 224 2 18 49 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 98 224 7 5 14 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 98 224 2 17 49 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 224
  (Polychromatic418967fa.accept_17_16_13_3_1_4677 33 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 224 2 16 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 224 (accept_3_2 31 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 224 2 15 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 98 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 224 14 2 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 224 (Polychromatic418967fa.accept_11_5_10_4_1_1157
  27 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 98 224 2 13 49 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 98 224
  (accept_3_2 25 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98 224 2 12 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 98 224
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 98 224 2 11 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 98 224 7 3 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 98 224 2 10 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 98 224 (accept_3_2 19 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 224 2 9 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 98 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 224 2 8 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 224
  (Polychromatic418967fa.accept_22_15_10_4_1_10294 15 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 98 224 14 1 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 98 224 (accept_3_2 13 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 98 224 2 6 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 98 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 98 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 98 224 2 5 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 98 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 9
  98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 224 2 4 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 98 224 7 1 14 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 98 224 2 3 49 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 98 224
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 98 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 98 224 2 2 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 98 224 (Polychromatic418967fa.accept_24_3_2_8_1_4572 3 98 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 224 2 1 49 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 224 (accept_3_2 1 98 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  224 (allA_of_3_0 97 97 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 224 (allA_succ_of_accept 95 96 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 96 224 2 47 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 96 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 96 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 96 224 4 23 24 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 224 (accept_3_2 91 96 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 224 2 45 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 224 (Polychromatic418967fa.accept_11_1_8_4_1_717 89
  96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 224 8 11 12 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 224
  (Polychromatic418967fa.accept_13_9_5_3_1_428 87 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 224 2 43 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 224 (accept_3_2 85 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 224 4 21 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 96 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 224 2 41 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 224 (Polychromatic418967fa.accept_18_9_6_8_1_2989
  81 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 224 16 5 6 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 224 (accept_3_2 79
  96 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 224 2 39 48 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 96 224 4 19 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 96 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 96 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 224 2 37 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 224 (accept_3_2 73 96 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 224 8 9 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 96 224 (Polychromatic418967fa.accept_13_6_5_3_1_426 71 96 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 224 2 35 48 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 224
  (Polychromatic418967fa.accept_15_9_6_14_1_2627 69 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 224 4 17 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 224 (accept_3_2 67 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96
  224 2 33 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  65 96 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 96 224 32 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 96 224 (Polychromatic418967fa.accept_13_11_5_3_1_889 63 96 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 224 2 31 48 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 224 (accept_3_2 61 96 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 224 4 15 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 59
  96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 224 2 29 48 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 96 224 8 7 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 96 224 (accept_3_2 55 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96
  224 2 27 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 96 224 (Polychromatic418967fa.accept_13_1_5_3_1_888 53 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 96 224 4 13 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 96 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 51 96 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 224 2 25 48 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 224 (accept_3_2 49 96 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 224 16 3 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 47
  96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 224 2 23 48 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 224 4 11 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 96 224 (accept_3_2 43 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96
  224 2 21 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 96 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 96 224 8 5 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 96 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 96 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 224 2 19 48 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 224 (accept_3_2 37 96 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 224 4 9 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 96 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 224 2 17 48 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 224
  (Polychromatic418967fa.accept_19_14_1_15_1_7914 33 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 224 32 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 224 (accept_3_2 31 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96
  224 2 15 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 96 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 96 224 4 7 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 224 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 96 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 224 2 13 48 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 224 (accept_3_2 25 96 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 224 8 3 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 96 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 224 2 11 48 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 224 4 5 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 224 (accept_3_2 19 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96
  224 2 9 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  96 224 (Polychromatic418967fa.accept_19_17_1_15_1_7901 17 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 224 16 1 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 96 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 96 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 224 2 7 48 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 224 (accept_3_2 13 96 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 224 4 3 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 96 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 224 2 5 48 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 224
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 224 8 1 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 224 (accept_3_2 7 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 224
  2 3 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96
  224 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 224 4 1 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 96 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 96 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 224 2 1 48 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 224 (accept_3_2 1 96 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 224
  (allA_succ_of_accept 94 95 224 (accept_3_2 94 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 224 (accept_3_2 91 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 224 (Polychromatic418967fa.accept_13_12_4_3_1_1528 90 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 224
  (Polychromatic418967fa.accept_10_9_5_4_1_966 89 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 224 (accept_3_2 88 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 86 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 224 (accept_3_2 85 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 224 (accept_3_2 82 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 80 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 224 (accept_3_2 79 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 224
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 77 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 224 (accept_3_2 76 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 224 (accept_3_2 73 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 224 (Polychromatic418967fa.accept_13_7_4_3_1_3064 72 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 224
  (Polychromatic418967fa.accept_10_1_5_4_1_276 71 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 224 (accept_3_2 70 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 224 (Polychromatic418967fa.accept_15_8_5_14_1_986 68 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 224 (accept_3_2 67 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 224 (accept_3_2 64 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 224 (accept_3_2 61 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 224
  (Polychromatic418967fa.accept_10_9_5_4_1_966 59 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 224 (accept_3_2 58 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 224 (accept_3_2 55 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 224 (Polychromatic418967fa.accept_15_9_5_14_1_973 54 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 224
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 53 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 224 (accept_3_2 52 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 224 (accept_3_2 49 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 224 (accept_3_2 46 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 224 (Polychromatic418967fa.accept_21_2_11_14_1_11805 44 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 224 (accept_3_2 43 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 95 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 224
  (Polychromatic418967fa.accept_10_1_5_4_1_276 41 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 224 (accept_3_2 40 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 224 (accept_3_2 37 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 224
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 35 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 224 (accept_3_2 34 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 224 (Polychromatic418967fa.accept_15_2_5_14_1_61 32 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 224 (accept_3_2 31 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 224 (accept_3_2 28 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 224 (accept_3_2 25 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 224
  (Polychromatic418967fa.accept_15_8_5_14_1_986 23 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 224 (accept_3_2 22 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 224 (accept_3_2 19 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 224 (Polychromatic418967fa.accept_21_18_11_14_1_8846 18 95 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 224
  (Polychromatic418967fa.accept_15_2_5_14_1_61 17 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 224 (accept_3_2 16 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 224 (accept_3_2 13 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 224 (accept_3_2 10 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 224 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 224 (accept_3_2 7 95 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 95 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 224
  (Polychromatic418967fa.accept_20_5_15_4_1_7635 5 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 224 (accept_3_2 4 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 95 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 224 (accept_3_2 1 95 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 224
  (allA_of_3_0 94 94 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 224 (allA_succ_of_accept 92 93 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 224 (accept_3_2 91 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 224 (accept_3_2 88 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 86 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 224 (accept_3_2 85 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 224 (Polychromatic418967fa.accept_18_12_3_8_1_6817 84 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 224 (accept_3_2 82 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 224 (Polychromatic418967fa.accept_17_13_8_3_1_7177 81 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 224
  (Polychromatic418967fa.accept_17_12_8_3_1_4646 80 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 224 (accept_3_2 79 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 224 (accept_3_2 76 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 224 (Polychromatic418967fa.accept_13_10_2_3_1_3025 75 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 224 (accept_3_2 73 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 224 (Polychromatic418967fa.accept_22_6_5_4_1_13342 72 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 224 (accept_3_2 70 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 224 (accept_3_2 67 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 224 (accept_3_2 64 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 224 (Polychromatic418967fa.accept_13_11_2_3_1_883 63 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 224
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 62 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 224 (accept_3_2 61 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 224 (accept_3_2 58 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 224 (accept_3_2 55 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 224 (Polychromatic418967fa.accept_11_10_5_4_1_711 54 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 224 (accept_3_2 52 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 224 (accept_3_2 49 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 224 (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 224 (accept_3_2 46 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 224 (Polychromatic418967fa.accept_18_9_3_8_1_5419 45 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 224
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 44 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 224 (accept_3_2 43 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 224 (accept_3_2 40 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 224 (accept_3_2 37 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 224 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 224 (accept_3_2 34 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 224 (accept_3_2 31 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 224 (accept_3_2 28 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 224
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 224 (accept_3_2 25 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 224 (accept_3_2 22 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 224 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 224 (accept_3_2 19 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 224 (accept_3_2 16 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 224 (accept_3_2 13 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 224 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 224 (accept_3_2 10 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 93 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 224
  (Polychromatic418967fa.accept_19_8_17_15_1_11952 8 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 224 (accept_3_2 7 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  224 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 224 (accept_3_2 4 93 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 224 (Polychromatic418967fa.accept_19_3_17_15_1_6459 3 93 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  93 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 224 (accept_3_2 1 93 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 224
  (allA_succ_of_accept 91 92 224 (accept_3_2 91 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  224 2 45 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 224 (Polychromatic418967fa.accept_13_11_1_3_1_910 89 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 224 4 22 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 92 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 224 2 43 46 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 224 (accept_3_2 85 92 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 224 4 21 23 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 224
  (Polychromatic418967fa.accept_13_5_1_3_1_878 83 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 224 2 41 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 224 (Polychromatic418967fa.accept_24_9_20_8_1_9900 81 92 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 224 4 20 23 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 224 (accept_3_2 79 92 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 224 2 39 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 77
  92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 224 4 19 23 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 224 2 37 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 92 224 (accept_3_2 73 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 92 224 4 18 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 92 224 (Polychromatic418967fa.accept_13_6_1_3_1_1522 71 92 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 224 2 35 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 69
  92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 224 4 17 23 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 224 (accept_3_2 67
  92 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 224 2 33 46 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 224
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 65 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 224 4 16 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 224 (Polychromatic418967fa.accept_13_11_1_3_1_910 63 92 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 224 2 31 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 224 (accept_3_2 61 92 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 224 4 15 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 92 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 224 2 29 46 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 224 4 14 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 92 224 (accept_3_2 55 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92
  224 2 27 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 92 224 (Polychromatic418967fa.accept_18_17_2_8_1_6800 53 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 92 224 4 13 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 92 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 224 2 25 46 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 224 (accept_3_2 49 92 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 224 4 12 23 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 47 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 224 2 23 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 92 224 (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 92 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 224 4 11 23 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 224 (accept_3_2 43 92 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 224 2 21 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 41
  92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 224 4 10 23 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 224 2 19 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 92 224 (accept_3_2 37 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 92 224 4 9 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 92 224 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 92 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 224 2 17 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 33
  92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 224 4 8 23 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 224 (accept_3_2 31
  92 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 224 2 15 46 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 224
  (Polychromatic418967fa.accept_17_12_7_3_1_1498 29 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 92 224 4 7 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 92 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 92 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 224 2 13 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 224 (accept_3_2 25 92 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 224 4 6 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 92 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 92 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 224 2 11 46 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 224 4 5 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 224 (accept_3_2 19 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  224 2 9 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 224 4 4 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 92 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 224 2 7 46 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 224 (accept_3_2 13 92 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 224 4 3 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 224 (Polychromatic418967fa.accept_13_11_1_3_1_910 11 92 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 224 2 5 46 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 224
  (Polychromatic418967fa.accept_24_9_20_8_1_9900 9 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 224 4 2 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 224 (accept_3_2 7 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 224
  2 3 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 92 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 224 4 1 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 92 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 224 2 1 46 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 224 (accept_3_2 1 92 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 224
  (allA_of_3_0 91 91 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 224 (allA_succ_of_accept 89 90 224
  (Polychromatic418967fa.accept_19_13_14_15_1_7924 89 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 90 224 2 44 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 90 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 87 90 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 224 2 43 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 224 (accept_3_2 85 90 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 224 2 42 45 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 224
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 83 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 90 224 2 41 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 90 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 81 90 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 90 224 2 40 45 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 224 (accept_3_2 79 90 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 224 2 39 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 224 (Polychromatic418967fa.accept_19_1_14_15_1_3704
  77 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 224 2 38 45 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 224
  (Polychromatic418967fa.accept_11_9_2_4_1_707 75 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 90 224 2 37 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 90 224 (accept_3_2 73 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 224 2 36 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 90 224 (Polychromatic418967fa.accept_20_11_10_4_1_7520 71 90 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 224 2 35 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 90 224 2 34 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 90 224 (accept_3_2 67 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 224 2 33 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 90 224 (Polychromatic418967fa.accept_20_5_10_4_1_4548 65 90 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 224 2 32 45 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 224 2 31 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 90 224 (accept_3_2 61 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 224 2 30 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 90 224 (Polychromatic418967fa.accept_17_8_5_3_1_2397 59 90 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 224 2 29 45 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 90 224 2 28 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 90 224 (accept_3_2 55 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 224 2 27 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 90 224 (Polychromatic418967fa.accept_11_9_2_4_1_707 53 90 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 224 2 26 45 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 224 2 25 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 90 224 (accept_3_2 49 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 224 2 24 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 90 224 (Polychromatic418967fa.accept_24_23_18_8_1_4564 47 90 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 224 2 23 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 224 2 22 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 90 224 (accept_3_2 43 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 224 2 21 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 90 224 (Polychromatic418967fa.accept_13_2_12_3_1_415 41 90 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 224 2 20 45 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 224
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 224 2 19 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 90 224 (accept_3_2 37 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 224 2 18 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 90 224 (Polychromatic418967fa.accept_13_9_12_3_1_907 35 90 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 224 2 17 45 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 224 2 16 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 90 224 (accept_3_2 31 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 224 2 15 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 224 (Polychromatic418967fa.accept_19_10_14_15_1_2478 29 90 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 224 2 14 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 224 2 13 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 90 224 (accept_3_2 25 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 224 2 12 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 90 224 (Polychromatic418967fa.accept_17_6_5_3_1_7134 23 90 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 224 2 11 45 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 224 2 10 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 90 224 (accept_3_2 19 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 224 2 9 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 90 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 224 2 8 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 224 2 7 45 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 224 (accept_3_2 13
  90 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 224 2 6 45 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 224
  (Polychromatic418967fa.accept_19_11_14_15_1_9276 11 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 224 2 5 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 90 224 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 90 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 224 2 4 45 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 224 (accept_3_2 7 90 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 224 2 3 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 224 (Polychromatic418967fa.accept_20_5_10_4_1_4548 5 90 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 224 2 2 45 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 224 2 1 45 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 224 (accept_3_2 1 90 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 224
  (allA_succ_of_accept 88 89 224 (accept_3_2 88 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 86 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 224 (accept_3_2 85 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 224 (Polychromatic418967fa.accept_17_16_4_3_1_3429 84 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 224
  (Polychromatic418967fa.accept_10_3_9_4_1_960 83 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 224 (accept_3_2 82 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 224 (Polychromatic418967fa.accept_13_2_11_3_1_873 80 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 224 (accept_3_2 79 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 78 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 224
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 77 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 224 (accept_3_2 76 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 224 (Polychromatic418967fa.accept_11_8_1_4_1_2318 74 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 224 (accept_3_2 73 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 224 (Polychromatic418967fa.accept_13_7_11_3_1_1540 72 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 224
  (Polychromatic418967fa.accept_19_14_13_15_1_2532 71 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 89 224 (accept_3_2 70 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 89 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 68 89 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 224 (accept_3_2 67 89 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 224 (Polychromatic418967fa.accept_13_1_11_3_1_901
  66 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 224
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 65 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 224 (accept_3_2 64 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 224 (accept_3_2 61 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 224 (Polychromatic418967fa.accept_13_8_11_3_1_3053 60 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 224
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 59 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 224 (accept_3_2 58 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 224 (Polychromatic418967fa.accept_18_2_17_8_1_1893 56 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 224 (accept_3_2 55 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 224 (Polychromatic418967fa.accept_13_2_11_3_1_873 54 89 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 224
  (Polychromatic418967fa.accept_10_3_9_4_1_960 53 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 224 (accept_3_2 52 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 224 (accept_3_2 49 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 224
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 47 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 224 (accept_3_2 46 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 224 (Polychromatic418967fa.accept_13_5_11_3_1_902 44 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 224 (accept_3_2 43 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 224 (Polychromatic418967fa.accept_19_4_13_15_1_3676 42 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 224
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 224 (accept_3_2 40 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 224 (accept_3_2 37 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 224 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 224
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 224 (accept_3_2 34 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 224 (Polychromatic418967fa.accept_21_11_5_14_1_4142 32 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 224 (accept_3_2 31 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 224 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 89 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 224
  (Polychromatic418967fa.accept_21_8_5_14_1_5660 29 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 224 (accept_3_2 28 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 224 (accept_3_2 25 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 224 (Polychromatic418967fa.accept_17_7_4_3_1_3456 24 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 224
  (Polychromatic418967fa.accept_10_3_9_4_1_960 23 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 224 (accept_3_2 22 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 224 (Polychromatic418967fa.accept_13_7_11_3_1_1540 20 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 224 (accept_3_2 19 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 89 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 224
  (Polychromatic418967fa.accept_19_17_13_15_1_1402 17 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 89 224 (accept_3_2 16 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 89 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 224 (accept_3_2 13 89 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 224
  (Polychromatic418967fa.accept_21_12_5_14_1_13341 12 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 224 (Polychromatic418967fa.accept_21_11_5_14_1_4142 11 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 224 (accept_3_2 10 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 224
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 224 (accept_3_2 7 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  224 (Polychromatic418967fa.accept_19_6_13_15_1_2406 6 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 89 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 224 (accept_3_2 4 89 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 89 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 89 224 (accept_3_2 1 89 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 224
  (allA_of_3_0 88 88 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 224 (allA_succ_of_accept 86 87 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 86 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 87 224 (accept_3_2 85 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  87 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 224 (accept_3_2 82 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 81 87 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 224
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 80 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 224 (accept_3_2 79 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  87 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 224 (accept_3_2 76 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 87 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 224 (accept_3_2 73 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 224 (accept_3_2 70 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 224 (Polychromatic418967fa.accept_15_9_12_14_1_963 69 87 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 224 (accept_3_2 67 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 224 (accept_3_2 64 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 63 87 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 62 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 224 (accept_3_2 61 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 224 (Polychromatic418967fa.accept_11_5_10_4_1_1157 60 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 224 (accept_3_2 58 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 87 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 224 (accept_3_2 55 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 224 (accept_3_2 52 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 51 87 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 224 (accept_3_2 49 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 224 (accept_3_2 46 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 224 (Polychromatic418967fa.accept_13_6_9_3_1_915 45 87 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 224
  (Polychromatic418967fa.accept_13_5_9_3_1_870 44 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 224 (accept_3_2 43 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 224 (accept_3_2 40 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 87 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 224 (accept_3_2 37 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 224 (Polychromatic418967fa.accept_21_15_3_14_1_4141 36 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 224 (accept_3_2 34 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 87 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 224 (accept_3_2 31 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 224 (accept_3_2 28 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 224 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 87 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 224
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 87 224 (accept_3_2 25 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 87 224 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 87 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 224 (accept_3_2 22 87 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 21
  87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 224 (accept_3_2 19 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 224 (accept_3_2 16 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 224 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 87 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 224 (accept_3_2 13 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 224 (accept_3_2 10 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 224 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 87 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 224
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 8 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 224 (accept_3_2 7 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  224 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 224 (accept_3_2 4 87 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 87 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  87 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 224 (accept_3_2 1 87 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 224
  (allA_succ_of_accept 85 86 224 (accept_3_2 85 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  224 2 42 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 224 2 41 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 224 (Polychromatic418967fa.accept_19_5_10_15_1_5076 81 86 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 224 2 40 43 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 224 (accept_3_2 79 86 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 224 2 39 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 224
  (Polychromatic418967fa.accept_12_5_2_8_1_172 77 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 224 2 38 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 86 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 224 2 37 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 224 (accept_3_2 73 86 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 224 2 36 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 224 (Polychromatic418967fa.accept_12_11_2_8_1_511
  71 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 224 2 35 43 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 224 2 34 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 86 224 (accept_3_2 67 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 86 224 2 33 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 86 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 86 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 224 2 32 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 224
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 63 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 224 2 31 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 224 (accept_3_2 61 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 224 2 30 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 86 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 224 2 29 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 224 2 28 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 86 224 (accept_3_2 55 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 224 2 27 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 86 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 224 2 26 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 224 2 25 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 224 (accept_3_2 49 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 224 2 24 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 86 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 224 2 23 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 224 2 22 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 224 (accept_3_2 43 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 224 2 21 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 86 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 224 2 20 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 224 2 19 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 86 224 (accept_3_2 37 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 224 2 18 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 86 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 224 2 17 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 224 2 16 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 86 224 (accept_3_2 31 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 224 2 15 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 86 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 224 2 14 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 224
  (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 86 224 2 13 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 86 224 (accept_3_2 25 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 224 2 12 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 86 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 224 2 11 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 224 2 10 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 86 224 (accept_3_2 19 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 224 2 9 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 86 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 224 2 8 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 224 2 7 43 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 224 (accept_3_2 13
  86 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 224 2 6 43 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 86 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 224 2 5 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 224 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 86 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 224 2 4 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 224 (accept_3_2 7 86 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 224 2 3 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 86 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 224 2 2 43 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 86
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 224 2 1 43 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 224 (accept_3_2 1 86
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 224
  (allA_of_3_0 85 85 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 224 (allA_succ_of_accept 83 84 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 224 2 41 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 84 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 81 84 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 224 4 20 21 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 224 (accept_3_2 79 84 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 224 2 39 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 84 224 7 11 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 84 224 4 19 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 224 (Polychromatic418967fa.accept_13_10_6_3_1_1515
  75 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 84 224 2 37 42 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 84 224
  (accept_3_2 73 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 224 4 18 21 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 224
  (Polychromatic418967fa.accept_22_5_18_4_1_327 71 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 84 224 14 5 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 84 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 84 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 224 4 17 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 224 (accept_3_2 67 84 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 224 2 33 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 84 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84 224 4 16 21 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 84 224 7 9 12 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 84 224 2 31 42 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 224
  (accept_3_2 61 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 224 4 15 21 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 84 224 2 29 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 84 224 (Polychromatic418967fa.accept_13_5_6_3_1_868 57 84 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 224 28 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 224 (accept_3_2 55 84 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 224 2 27 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 224 (Polychromatic418967fa.accept_13_1_6_3_1_1547 53 84 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 224 4 13 21 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 224 2 25 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 84 224 7 7 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 84 224 4 12 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 84 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 84 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 224 2 23 42 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 224
  (Polychromatic418967fa.accept_19_7_8_15_1_2448 45 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 84 224 4 11 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 84 224 (accept_3_2 43 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84
  224 14 3 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  84 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 84 224 4 10 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 84 224 (Polychromatic418967fa.accept_18_3_12_8_1_5415 39 84 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 224 2 19 42 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 224 (accept_3_2 37 84 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 224 4 9 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 84 224 7 5 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 84 224 2 17 42 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 224 4 8 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 224 (accept_3_2 31 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84
  224 2 15 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 84 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 84 224 28 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 84 224 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 84 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 224 2 13 42 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 224 (accept_3_2 25 84 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 224 4 6 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 224 2 11 42 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84 224 7 3 12 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84 224 4 5 21 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 224 (accept_3_2 19
  84 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 224 2 9 42 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 224
  (Polychromatic418967fa.accept_19_17_8_15_1_6448 17 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 84 224 4 4 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 84 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 224 14 1 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 224 (accept_3_2 13 84 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 84 224 4 3 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 84 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 224 2 5 42 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 224
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 84 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 224 4 2 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 84 224 7 1 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 84 224 2 3 42 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 224 4 1 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 84 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 224 2 1 42 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 224 (accept_3_2 1 84 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 224
  (allA_succ_of_accept 82 83 224 (accept_3_2 82 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 224 (Polychromatic418967fa.accept_13_2_5_3_1_406 80 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 224 (accept_3_2 79 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 224 (accept_3_2 76 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 224 (accept_3_2 73 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 224 (Polychromatic418967fa.accept_21_9_20_14_1_4139 72 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 224
  (Polychromatic418967fa.accept_13_6_5_3_1_426 71 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 224 (accept_3_2 70 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 224 (accept_3_2 67 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 224
  (Polychromatic418967fa.accept_15_5_8_14_1_432 65 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 224 (accept_3_2 64 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 224 (accept_3_2 61 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 224 (accept_3_2 58 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 224 (Polychromatic418967fa.accept_19_18_7_15_1_3733 56 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 224 (accept_3_2 55 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 224 (Polychromatic418967fa.accept_13_2_5_3_1_406 54 83 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 224
  (Polychromatic418967fa.accept_13_1_5_3_1_888 53 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 224 (accept_3_2 52 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 224 (accept_3_2 49 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 224
  (Polychromatic418967fa.accept_10_7_3_4_1_978 47 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 224 (accept_3_2 46 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 224 (Polychromatic418967fa.accept_21_2_20_14_1_5649 44 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 224 (accept_3_2 43 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 83 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 224 (accept_3_2 40 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 224 (accept_3_2 37 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 224 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 224
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 224 (accept_3_2 34 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 224 (accept_3_2 31 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 224
  (Polychromatic418967fa.accept_10_9_3_4_1_985 29 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 224 (accept_3_2 28 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 224 (accept_3_2 25 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 224 (accept_3_2 22 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 224 (Polychromatic418967fa.accept_15_5_8_14_1_432 20 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 224 (accept_3_2 19 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 224 (Polychromatic418967fa.accept_17_1_15_3_1_1501 18 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 224
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 224 (accept_3_2 16 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 224 (accept_3_2 13 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 224
  (Polychromatic418967fa.accept_13_11_5_3_1_889 11 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 224 (accept_3_2 10 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 224 (Polychromatic418967fa.accept_13_8_5_3_1_427 8 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 224 (accept_3_2 7 83 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 224 (accept_3_2 4 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 224 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 83 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 224 (accept_3_2 1 83 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 224 (allA_of_3_0 82 82 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 224
  (allA_succ_of_accept 80 81 224 (Polychromatic418967fa.accept_15_5_6_14_1_1721 80 81 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 224 (accept_3_2 79 81 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 81 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 224 (accept_3_2 76 81
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 224
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 75 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 224 (Polychromatic418967fa.accept_19_17_5_15_1_7921 74 81 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 224 (accept_3_2 73 81 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 224 (Polychromatic418967fa.accept_17_4_13_3_1_7166 72 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 81 224 (accept_3_2 70 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  81 224 (Polychromatic418967fa.accept_15_9_6_14_1_2627 69 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 81 224 (Polychromatic418967fa.accept_15_8_6_14_1_975 68 81 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 224 (accept_3_2 67 81 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 224 (accept_3_2 64 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  81 224 (Polychromatic418967fa.accept_19_6_5_15_1_13340 63 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 81 224 (Polychromatic418967fa.accept_21_20_18_14_1_10455 62 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 224 (accept_3_2 61 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 224 (Polychromatic418967fa.accept_18_6_9_8_1_6812 60 81 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 224 (accept_3_2 58 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447 57 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 224 (Polychromatic418967fa.accept_26_4_3_16_1_13339 56 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 224 (accept_3_2 55 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 81 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 224 (accept_3_2 52 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 224 (Polychromatic418967fa.accept_20_11_1_4_1_7543 51 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 224 (Polychromatic418967fa.accept_15_5_6_14_1_1721 50 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 224 (accept_3_2 49 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 224 (Polychromatic418967fa.accept_19_10_5_15_1_6443 48 81
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 224 (accept_3_2 46 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 224 (Polychromatic418967fa.accept_17_10_13_3_1_1425 44 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 224 (accept_3_2 43 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 81 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 224 (accept_3_2 40 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 224 (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 224 (Polychromatic418967fa.accept_15_8_6_14_1_975 38 81 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 224 (accept_3_2 37 81 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 224 (Polychromatic418967fa.accept_19_17_5_15_1_7921 36 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 224 (accept_3_2 34 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 224 (Polychromatic418967fa.accept_17_16_13_3_1_4677 33 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 224 (Polychromatic418967fa.accept_21_11_18_14_1_5646 32 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 224 (accept_3_2 31 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 81 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 224 (accept_3_2 28 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 224 (Polychromatic418967fa.accept_21_5_18_14_1_2793 26 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 224 (accept_3_2 25 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 224 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 81
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 224 (accept_3_2 22 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 224 (Polychromatic418967fa.accept_17_4_13_3_1_7166 21 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 224 (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 224 (accept_3_2 19 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 81 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 224 (accept_3_2 16 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 224 (Polychromatic418967fa.accept_22_14_15_4_1_8623 14 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 224 (accept_3_2 13 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 224 (Polychromatic418967fa.accept_19_12_5_15_1_13338 12 81
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 224 (accept_3_2 10 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 224 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 224 (Polychromatic418967fa.accept_15_8_6_14_1_975 8 81 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 224 (accept_3_2 7 81 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 81 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 224 (accept_3_2 4 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  224 (Polychromatic418967fa.accept_18_3_9_8_1_2977 3 81 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 81 224 (Polychromatic418967fa.accept_26_2_3_16_1_13337 2 81 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 224 (accept_3_2 1 81 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 81 224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 224 (allA_succ_of_accept 79 80 224 (accept_3_2 79 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 80 224 2 39 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 80 224 (Polychromatic418967fa.accept_13_12_2_3_1_1527 77 80 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 80 224 4 19 20 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 80 224
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 75 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 80 224 2 37 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 80 224 (accept_3_2 73 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 80 224 8 9 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 80 224 (Polychromatic418967fa.accept_19_14_4_15_1_2434 71 80 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 80 224 2 35 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 224 (Polychromatic418967fa.accept_15_9_5_14_1_973
  69 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 224 4 17 20 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 224 (accept_3_2 67
  80 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 224 2 33 40 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 224
  (Polychromatic418967fa.accept_19_8_4_15_1_1414 65 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 80 224 16 4 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 80 224 (Polychromatic418967fa.accept_13_11_2_3_1_883 63 80 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 224 2 31 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 224 (accept_3_2 61 80 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 224 4 15 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 224 (Polychromatic418967fa.accept_17_8_12_3_1_5927 59 80 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 224 2 29 40 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 224
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 57 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 224 8 7 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 80 224 (accept_3_2 55 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80
  224 2 27 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 80 224 (Polychromatic418967fa.accept_13_1_2_3_1_911 53 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 80 224 4 13 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 80 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 80 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 224 2 25 40 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 224 (accept_3_2 49 80 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 224 16 3 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 224 (Polychromatic418967fa.accept_15_2_5_14_1_61 47
  80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 224 2 23 40 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 224
  (Polychromatic418967fa.accept_21_3_17_14_1_8828 45 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 224 4 11 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 224 (accept_3_2 43 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  224 2 21 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 80 224 (Polychromatic418967fa.accept_17_7_12_3_1_4693 41 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 224 8 5 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 80 224 (Polychromatic418967fa.accept_15_9_5_14_1_973 39 80 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 224 2 19 40 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 224 (accept_3_2 37 80 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 224 4 9 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 224 (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 80 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 224 2 17 40 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 224
  (Polychromatic418967fa.accept_19_14_4_15_1_2434 33 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 224 16 2 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 224 (accept_3_2 31 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  224 2 15 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 80 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 224 4 7 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 224 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 80 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 224 2 13 40 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 224 (accept_3_2 25 80 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 224 8 3 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 224 (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 80 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 224 2 11 40 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 224
  (Polychromatic418967fa.accept_15_6_5_14_1_429 21 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 224 4 5 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 224 (accept_3_2 19 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  224 2 9 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 224 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 224 16 1 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 224 (Polychromatic418967fa.accept_17_15_12_3_1_8478 15 80 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 224 2 7 40 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 224 (accept_3_2 13 80 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 224 4 3 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 224 (Polychromatic418967fa.accept_13_11_2_3_1_883
  11 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 224 2 5 40 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 224
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 224 8 1 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 224 (accept_3_2 7 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 224
  2 3 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  224 (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 80 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 80 224 4 1 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 80 224 (Polychromatic418967fa.accept_21_3_17_14_1_8828 3 80 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 224 2 1 40 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 224 (accept_3_2 1 80 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 80 224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 79 224 (allA_of_3_0 79 79 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 224
  (allA_succ_of_accept 77 78 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 78 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 224 2 38 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 78 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 75
  78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 224 2 37 39 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 224 (accept_3_2 73
  78 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 224 2 36 39 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 224
  (Polychromatic418967fa.accept_15_11_3_14_1_971 71 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 224 2 35 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 78 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 69 78 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 78 224 2 34 39 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 224 (accept_3_2 67 78 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 224 2 33 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 65
  78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 224 2 32 39 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 224
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 224 2 31 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 78 224 (accept_3_2 61 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 224 2 30 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 78 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 224 2 29 39 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 224 2 28 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 78 224 (accept_3_2 55 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 224 2 27 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 224 (Polychromatic418967fa.accept_24_5_6_8_1_11665 53 78 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 224 2 26 39 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 224 2 25 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 78 224 (accept_3_2 49 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 224 2 24 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 78 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 224 2 23 39 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 224 2 22 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 78 224 (accept_3_2 43 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 224 2 21 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 78 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 224 2 20 39 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 224 2 19 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 78 224 (accept_3_2 37 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 224 2 18 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 224 (Polychromatic418967fa.accept_22_13_12_4_1_10296 35 78 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 224 2 17 39 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 224 2 16 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 78 224 (accept_3_2 31 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 224 2 15 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 78 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 224 2 14 39 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 224 2 13 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 78 224 (accept_3_2 25 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 224 2 12 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 78 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 224 2 11 39 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 224 2 10 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 78 224 (accept_3_2 19 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 224 2 9 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 224 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 78 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 224 2 8 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 224 2 7 39 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 224 (accept_3_2 13
  78 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 224 2 6 39 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 78 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 224 2 5 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 78 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 78 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 224 2 4 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 224 (accept_3_2 7 78 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 78 224 2 3 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 78 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 78 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 224 2 2 39 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 78
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 224 2 1 39 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 224 (accept_3_2 1 78
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 224
  (allA_succ_of_accept 76 77 224 (accept_3_2 76 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 77 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 224 (accept_3_2 73 77 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 77 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 224
  (Polychromatic418967fa.accept_10_1_7_4_1_968 71 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 77 224 7 10 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 77 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 224 (Polychromatic418967fa.accept_18_14_5_8_1_1880 68 77
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 224 (accept_3_2 67 77 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 66
  77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 224 (accept_3_2 64 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 77
  224 7 9 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62
  77 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 62 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 77 224 (accept_3_2 61 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 77 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 77 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 224 (Polychromatic418967fa.accept_19_2_1_15_1_2494 59 77
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 224 (accept_3_2 58 77 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57
  77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 77 224 7 8 11 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 77 224 (accept_3_2 55
  77 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 224
  (Polychromatic418967fa.accept_13_2_12_3_1_415 54 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 77 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 53 77 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 224 (accept_3_2 52 77 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 77 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 77 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 224 (Polychromatic418967fa.accept_12_2_5_8_1_159
  50 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 77 224 7 7 11 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 77 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 77 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 77 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 224 (accept_3_2 46 77 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 77 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 224 (Polychromatic418967fa.accept_17_10_9_3_1_7144
  44 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 224 (accept_3_2 43
  77 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 77 224 7 6 11 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 77 224
  (Polychromatic418967fa.accept_10_1_7_4_1_968 41 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 224 (accept_3_2 40 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 77 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 224 (accept_3_2 37 77 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 224 (Polychromatic418967fa.accept_19_17_1_15_1_7901 36 77 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 77 224 7 5 11 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 77 224 (accept_3_2 34 77 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 77 224 (accept_3_2 31 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  77 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 77 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 77 224 7 4 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 77 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27
  77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 224 (accept_3_2 25 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 77 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 224 (accept_3_2 22 77 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 77 224 7 3 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 77 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 224 (accept_3_2 19 77 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 224 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 77
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 224
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 224 (accept_3_2 16 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 77 224 7 2 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 77 224 (accept_3_2 13 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 77 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 224 (accept_3_2 10 77 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 224
  (Polychromatic418967fa.accept_19_8_1_15_1_2496 8 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 77 224 7 1 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 77 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 224 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 77 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 224 (accept_3_2 4 77 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 224 (accept_3_2 1 77 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 76 224 (allA_of_3_0 76 76
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 224 (allA_succ_of_accept 74 75 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 224 (accept_3_2 73 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 224 (Polychromatic418967fa.accept_13_7_10_3_1_1505 72 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 224 (accept_3_2 70 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 75 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 224 (accept_3_2 67 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 224 (accept_3_2 64 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 224 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 75 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 224
  (Polychromatic418967fa.accept_20_2_15_4_1_7575 62 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 224 (accept_3_2 61 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 224 (accept_3_2 58 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 224 (Polychromatic418967fa.accept_11_2_9_4_1_310 57 75 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 224 (accept_3_2 55 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 224 (accept_3_2 52 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 75 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 224 (accept_3_2 49 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 224 (Polychromatic418967fa.accept_18_12_3_8_1_6817 48 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 224 (accept_3_2 46 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 224 (Polychromatic418967fa.accept_13_6_10_3_1_897 45 75 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 224
  (Polychromatic418967fa.accept_17_10_7_3_1_727 44 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 224 (accept_3_2 43 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 224 (accept_3_2 40 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 75 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 224 (accept_3_2 37 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 224 (accept_3_2 34 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 224 (accept_3_2 31 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 224 (accept_3_2 28 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 224 (Polychromatic418967fa.accept_17_10_7_3_1_727 27 75 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 224
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 224 (accept_3_2 25 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 224 (accept_3_2 22 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 224 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 75 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 224 (accept_3_2 19 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 224 (accept_3_2 16 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 75 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 224 (accept_3_2 13 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 224 (Polychromatic418967fa.accept_17_12_7_3_1_1498 12 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 224 (accept_3_2 10 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 75 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 224
  (Polychromatic418967fa.accept_21_8_12_14_1_10464 8 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 224 (accept_3_2 7 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  224 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 224 (accept_3_2 4 75 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 224 (Polychromatic418967fa.accept_19_3_18_15_1_3711 3 75 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  75 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 224 (accept_3_2 1 75 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 224 (allA_succ_of_accept
  73 74 224 (accept_3_2 73 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 224 2 36 37 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 224
  (Polychromatic418967fa.accept_12_11_2_8_1_511 71 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 224 2 35 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 74 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 74 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 224 2 34 37 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 224 (accept_3_2 67 74 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 224 2 33 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 65
  74 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 224 2 32 37 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 224
  (Polychromatic418967fa.accept_20_3_14_4_1_7632 63 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 224 2 31 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 74 224 (accept_3_2 61 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 74 224 2 30 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 74 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 74 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 224 2 29 37 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 224 2 28 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 74 224 (accept_3_2 55 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 74 224 2 27 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 74 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 224 2 26 37 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 224 2 25 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 74 224 (accept_3_2 49 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 74 224 2 24 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 74 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 74 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 224 2 23 37 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 224
  (Polychromatic418967fa.accept_11_1_8_4_1_717 45 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 224 2 22 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 74 224 (accept_3_2 43 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 74 224 2 21 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 74 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 74 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 224 2 20 37 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 224 2 19 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 74 224 (accept_3_2 37 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 74 224 2 18 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 74 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 74 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 224 2 17 37 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 224 2 16 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 74 224 (accept_3_2 31 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 224 2 15 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 29 74 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 224 2 14 37 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 224
  (Polychromatic418967fa.accept_19_8_17_15_1_11952 27 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 74 224 2 13 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 74 224 (accept_3_2 25 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 224 2 12 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 74 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 224 2 11 37 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 224 2 10 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 224 (accept_3_2 19 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 224 2 9 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 74 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 224 2 8 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 15
  74 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 224 2 7 37 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 224 (accept_3_2 13
  74 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 224 2 6 37 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 224
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 74 224 2 5 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 74 224 (Polychromatic418967fa.accept_17_9_6_3_1_2398 9 74 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 224 2 4 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 224 (accept_3_2 7 74 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 224 2 3 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 74 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 224 2 2 37 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 74
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 224 2 1 37 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 224 (accept_3_2 1 74
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 224 (allA_of_3_0 73 73 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 224 (allA_succ_of_accept 71 72 224
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 71 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 72 224 2 35 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 72 224 (Polychromatic418967fa.accept_13_4_7_3_1_92 69 72 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 224 4 17 18 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 224 (accept_3_2 67 72 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 224 2 33 36 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 224
  (Polychromatic418967fa.accept_21_2_9_14_1_4189 65 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 72 224 8 8 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 72 224 (Polychromatic418967fa.accept_13_11_7_3_1_894 63 72 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 224 2 31 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 224 (accept_3_2 61 72 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 224 4 15 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 224 (Polychromatic418967fa.accept_21_17_9_14_1_5700 59 72
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 224 2 29 36 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 72 224 8 7 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 72 224 (accept_3_2 55 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72
  224 2 27 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 72 224 (Polychromatic418967fa.accept_13_1_7_3_1_1503 53 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 72 224 4 13 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 72 224 (Polychromatic418967fa.accept_27_24_18_8_1_13336 51 72 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 224 2 25 36 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 224 (accept_3_2 49 72 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 224 8 6 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 47
  72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 224 2 23 36 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 224
  (Polychromatic418967fa.accept_21_3_9_14_1_5701 45 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 224 4 11 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 224 (accept_3_2 43 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  224 2 21 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 72 224 (Polychromatic418967fa.accept_15_11_12_14_1_2612 41 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 224 8 5 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 72 224 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 72 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 224 2 19 36 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 224 (accept_3_2 37 72 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 224 4 9 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 224 (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 72 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 224 2 17 36 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 224
  (Polychromatic418967fa.accept_17_16_4_3_1_3429 33 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 224 8 4 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 224 (accept_3_2 31 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  224 2 15 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 72 224 (Polychromatic418967fa.accept_26_3_20_16_1_9717 29 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 224 4 7 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 72 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 224 2 13 36 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 224 (accept_3_2 25 72 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 224 8 3 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 224 (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 72 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 224 2 11 36 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 224
  (Polychromatic418967fa.accept_13_8_7_3_1_430 21 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 224 4 5 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 224 (accept_3_2 19 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  224 2 9 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 224 8 2 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 224 (Polychromatic418967fa.accept_21_15_9_14_1_10462 15 72 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 224 2 7 36 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 224 (accept_3_2 13 72 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 224 4 3 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 224 (Polychromatic418967fa.accept_13_11_7_3_1_894
  11 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 224 2 5 36 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 224
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 224 8 1 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 224 (accept_3_2 7 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 224
  2 3 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  224 (Polychromatic418967fa.accept_21_5_9_14_1_7247 5 72 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 224 4 1 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 224 (Polychromatic418967fa.accept_21_3_9_14_1_5701 3 72 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 224 2 1 36 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 224 (accept_3_2 1 72 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 224 (allA_succ_of_accept 70 71 224 (accept_3_2 70 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 71 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 224 (Polychromatic418967fa.accept_19_11_14_15_1_9276 68 71
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 224 (accept_3_2 67 71 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 224 (Polychromatic418967fa.accept_13_1_6_3_1_1547
  66 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 224
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 65 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 224 (accept_3_2 64 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 71 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 224 (accept_3_2 61 71 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 224 (Polychromatic418967fa.accept_24_12_23_8_1_13335 60 71 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 224
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 59 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 224 (accept_3_2 58 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 224 (Polychromatic418967fa.accept_18_2_17_8_1_1893 56 71 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 224 (accept_3_2 55 71 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 224 (Polychromatic418967fa.accept_11_10_5_4_1_711 54 71 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 224
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 53 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 224 (accept_3_2 52 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 71 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 224 (accept_3_2 49 71 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 224 (Polychromatic418967fa.accept_13_9_6_3_1_1514 48 71 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 224
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 47 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 224 (accept_3_2 46 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 224 (Polychromatic418967fa.accept_13_5_6_3_1_868 44 71 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 224 (accept_3_2 43 71 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 224 (Polychromatic418967fa.accept_15_12_11_14_1_3464 42 71 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 224
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 41 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 224 (accept_3_2 40 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 71 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 224 (accept_3_2 37 71 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 224 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 71 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 224
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 224 (accept_3_2 34 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 224 (Polychromatic418967fa.accept_11_10_5_4_1_711 32 71 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 224 (accept_3_2 31 71 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 224 (Polychromatic418967fa.accept_19_11_14_15_1_9276 30 71 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 224
  (Polychromatic418967fa.accept_19_10_14_15_1_2478 29 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 71 224 (accept_3_2 28 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 71 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 71 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 224 (accept_3_2 25 71 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 224 (Polychromatic418967fa.accept_21_3_8_14_1_8864
  24 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 224
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 224 (accept_3_2 22 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 224 (Polychromatic418967fa.accept_18_2_17_8_1_1893 20 71 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 224 (accept_3_2 19 71 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 224 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 71 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 224
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 224 (accept_3_2 16 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 71 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 224 (accept_3_2 13 71 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 224 (Polychromatic418967fa.accept_15_12_11_14_1_3464 12 71 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 224
  (Polychromatic418967fa.accept_19_11_14_15_1_9276 11 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 71 224 (accept_3_2 10 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 71 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 224 (Polychromatic418967fa.accept_23_8_2_17_1_13334 8 71 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 224 (accept_3_2 7 71 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 224 (Polychromatic418967fa.accept_21_6_8_14_1_10446
  6 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 224
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 224 (accept_3_2 4 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 71 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 224 (accept_3_2 1 71 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 224
  (allA_of_3_0 70 70 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 224 (allA_succ_of_accept 68 69 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 224 (accept_3_2 67 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 224 (accept_3_2 64 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 69 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 224
  (Polychromatic418967fa.accept_11_7_3_4_1_729 62 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 224 (accept_3_2 61 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 224 (Polychromatic418967fa.accept_17_9_1_3_1_4626 60 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 224 (accept_3_2 58 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 69 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 224 (accept_3_2 55 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 224 (accept_3_2 52 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 69 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 224 (accept_3_2 49 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 224 (accept_3_2 46 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 69 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 224
  (Polychromatic418967fa.accept_19_6_12_15_1_7895 44 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 224 (accept_3_2 43 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 224 (accept_3_2 40 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 69 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 224 (accept_3_2 37 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 224 (accept_3_2 34 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 69 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 224 (accept_3_2 31 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 224 (accept_3_2 28 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 224 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 69 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 224
  (Polychromatic418967fa.accept_17_9_1_3_1_4626 26 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 224 (accept_3_2 25 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 224 (Polychromatic418967fa.accept_19_5_12_15_1_9244 24 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 224 (accept_3_2 22 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 224 (accept_3_2 19 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 224 (accept_3_2 16 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 69 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 224 (accept_3_2 13 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 224 (accept_3_2 10 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 224 (Polychromatic418967fa.accept_17_9_1_3_1_4626 9 69 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 224
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 224 (accept_3_2 7 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  224 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 224 (accept_3_2 4 69 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 69 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  69 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 224 (accept_3_2 1 69 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 224 (allA_succ_of_accept 67 68
  224 (accept_3_2 67 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 224 2 33 34 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 224 4 16 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 224 (Polychromatic418967fa.accept_19_6_11_15_1_2527 63 68 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 224 2 31 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 224 (accept_3_2 61 68 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 224 4 15 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 68 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 224 2 29 34 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 224 4 14 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 224 (accept_3_2 55 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  224 2 27 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 68 224 (Polychromatic418967fa.accept_11_9_2_4_1_707 53 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 224 4 13 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 68 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 224 2 25 34 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 224 (accept_3_2 49 68 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 224 4 12 17 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 224 2 23 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 68 224 (Polychromatic418967fa.accept_19_7_11_15_1_2461 45 68 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 224 4 11 17 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 224 (accept_3_2 43 68 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 224 2 21 34 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 224
  (Polychromatic418967fa.accept_18_5_14_8_1_2966 41 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 68 224 4 10 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 68 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 68 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 224 2 19 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 224 (accept_3_2 37 68 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 224 4 9 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 68 224 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 68 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 224 2 17 34 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 224 4 8 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 224 (accept_3_2 31 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  224 2 15 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 68 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 224 4 7 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 68 224 (Polychromatic418967fa.accept_22_5_2_4_1_8626 27 68 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 224 2 13 34 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 224 (accept_3_2 25 68 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 224 4 6 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 224 (Polychromatic418967fa.accept_18_5_14_8_1_2966 23 68 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 224 2 11 34 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 224 4 5 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 224 (accept_3_2 19 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  224 2 9 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 224 4 4 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 68 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 224 2 7 34 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 224 (accept_3_2 13 68 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 224 4 3 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 68 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 224 2 5 34 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 224 4 2 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 224 (accept_3_2 7 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 224
  2 3 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  224 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 68 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 68 224 4 1 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 68 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 68 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 224 2 1 34 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 224 (accept_3_2 1 68 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 68 224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  67 224 (allA_of_3_0 67 67 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 224 (allA_succ_of_accept 65 66
  224 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 224 2 32 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 66 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 66 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 224 2 31 33 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 224 (accept_3_2 61 66 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 224 2 30 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 59
  66 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 224 2 29 33 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 224 2 28 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 66 224 (accept_3_2 55 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 224 2 27 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 224 (Polychromatic418967fa.accept_15_8_6_14_1_975 53 66 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 224 2 26 33 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 224 2 25 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 66 224 (accept_3_2 49 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 224 2 24 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 66 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 224 2 23 33 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 224 2 22 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 66 224 (accept_3_2 43 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 224 2 21 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 66 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 224 2 20 33 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 224 2 19 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 66 224 (accept_3_2 37 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 224 2 18 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 66 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 224 2 17 33 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 224 2 16 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 66 224 (accept_3_2 31 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 224 2 15 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 66 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 224 2 14 33 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 224 2 13 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 66 224 (accept_3_2 25 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 224 2 12 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 66 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 224 2 11 33 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 224 2 10 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 66 224 (accept_3_2 19 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 224 2 9 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 224 (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 66 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 224 2 8 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  66 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 224 2 7 33 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 224 (accept_3_2 13
  66 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 224 2 6 33 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 66 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 224 2 5 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 66 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 66 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 224 2 4 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 224 (accept_3_2 7 66 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 66 224 2 3 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 66 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 66 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 224 2 2 33 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  66 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 224 2 1 33 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 224 (accept_3_2 1 66
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 224 (allA_succ_of_accept 64 65 224
  (accept_3_2 64 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 65 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 224 (accept_3_2 61 65 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 59
  65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 224 (accept_3_2 58 65
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 224 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 224
  (Polychromatic418967fa.accept_10_6_5_4_1_571 56 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 65 224 (accept_3_2 55 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  65 224 (Polychromatic418967fa.accept_15_9_5_14_1_973 54 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 65 224 (Polychromatic418967fa.accept_15_8_5_14_1_986 53 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 224 (accept_3_2 52 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 65 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 65 224 (accept_3_2 49 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 224 (Polychromatic418967fa.accept_15_2_5_14_1_61 47 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 224 (accept_3_2 46 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 224
  (Polychromatic418967fa.accept_23_21_19_17_1_11738 44 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 65 224 (accept_3_2 43 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 65 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 65 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 65 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 224 (accept_3_2 40 65 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39
  65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 224
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 38 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 224 (accept_3_2 37 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 224 (Polychromatic418967fa.accept_19_16_8_15_1_6447 35 65 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 224 (accept_3_2 34 65 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 224 (accept_3_2 31 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 29 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 224 (accept_3_2 28 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 224
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 224 (accept_3_2 25 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 224 (accept_3_2 22 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 224
  (Polychromatic418967fa.accept_19_1_8_15_1_3786 20 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 224 (accept_3_2 19 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 224 (Polychromatic418967fa.accept_23_18_19_17_1_5029 18 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 224 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 224 (accept_3_2 16 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 224 (accept_3_2 13 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 224 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 224 (accept_3_2 10 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 224
  (Polychromatic418967fa.accept_15_8_5_14_1_986 8 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 224 (accept_3_2 7 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  224 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 65 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 224 (accept_3_2 4 65 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  65 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 224 (accept_3_2 1 65 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 224 (allA_of_3_0 64 64 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 224 (allA_succ_of_accept 62 63 224
  (Polychromatic418967fa.accept_11_7_8_4_1_718 62 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 224 (accept_3_2 61 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 224 (Polychromatic418967fa.accept_13_8_11_3_1_3053 60 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 224 (accept_3_2 58 63 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 63 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 63 224 7 8 9 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 63 224 (accept_3_2 55 63 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 63 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 224 (accept_3_2 52 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  63 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 51 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 63 224 (Polychromatic418967fa.accept_19_12_6_15_1_5064 50 63 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63 224 7 7 9 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 63 224
  (Polychromatic418967fa.accept_19_10_6_15_1_6444 48 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 63 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 224 (accept_3_2 46 63 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 63 224 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 63 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 224 (Polychromatic418967fa.accept_13_5_11_3_1_902
  44 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 224 (accept_3_2 43
  63 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 224 7 6 9 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 224 (accept_3_2 40 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  63 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 63 224 (Polychromatic418967fa.accept_22_16_19_4_1_10142 38 63 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 224 (accept_3_2 37 63 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 224 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 63
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 63 224 7 5 9 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 63 224 (accept_3_2 34
  63 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 224
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 33 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 224 (Polychromatic418967fa.accept_15_2_3_14_1_972 32 63 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 224 (accept_3_2 31 63 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63 224 7 4 9 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 63 224
  (Polychromatic418967fa.accept_10_7_3_4_1_978 27 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 224 (Polychromatic418967fa.accept_15_11_3_14_1_971 26 63 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 224 (accept_3_2 25 63 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 224 (Polychromatic418967fa.accept_17_7_12_3_1_4693 24 63 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 224 (accept_3_2 22 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63
  224 7 3 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  63 224 (Polychromatic418967fa.accept_13_7_11_3_1_1540 20 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 63 224 (accept_3_2 19 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 63 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 63 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 224 (accept_3_2 16 63 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 224 (Polychromatic418967fa.accept_13_2_11_3_1_873
  15 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 63 224 7 2 9 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 63 224 (accept_3_2 13
  63 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 224
  (Polychromatic418967fa.accept_11_1_8_4_1_717 12 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 63 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 224 (accept_3_2 10 63 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 63 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 63 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 224 (Polychromatic418967fa.accept_13_8_11_3_1_3053
  8 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 224 7 1 9 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 63 224
  (Polychromatic418967fa.accept_12_6_3_8_1_512 6 63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 224 (accept_3_2 4 63 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 224 (Polychromatic418967fa.accept_18_3_9_8_1_2977 3 63 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 224 (Polychromatic418967fa.accept_13_2_11_3_1_873 2
  63 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 224 (accept_3_2 1 63 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 224 (allA_succ_of_accept 61 62 224
  (accept_3_2 61 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 224 2 30 31 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 224
  (Polychromatic418967fa.accept_12_11_2_8_1_511 59 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 224 2 29 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 62 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 57 62 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 224 2 28 31 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 224 (accept_3_2 55 62 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 224 2 27 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 53
  62 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 224 2 26 31 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 224
  (Polychromatic418967fa.accept_21_9_20_14_1_4139 51 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 224 2 25 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 62 224 (accept_3_2 49 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 62 224 2 24 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 62 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 62 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 224 2 23 31 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 224
  (Polychromatic418967fa.accept_13_6_10_3_1_897 45 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 224 2 22 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 224 (accept_3_2 43 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 224 2 21 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 224 (Polychromatic418967fa.accept_11_8_7_4_1_3011 41 62 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 224 2 20 31 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 224
  (Polychromatic418967fa.accept_19_1_5_15_1_3722 39 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 224 2 19 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 224 (accept_3_2 37 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 224 2 18 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 62 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 224 2 17 31 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 224
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 33 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 224 2 16 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 62 224 (accept_3_2 31 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 62 224 2 15 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 62 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 224 2 14 31 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 224 2 13 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 62 224 (accept_3_2 25 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 224 2 12 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 62 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 224 2 11 31 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 224
  (Polychromatic418967fa.accept_24_21_14_8_1_13333 21 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 62 224 2 10 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 62 224 (accept_3_2 19 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 224 2 9 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 62 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 224 2 8 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 224 (Polychromatic418967fa.accept_13_2_10_3_1_1538
  15 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 224 2 7 31 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 224 (accept_3_2 13
  62 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 224 2 6 31 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 224
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 62 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 224 2 5 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 224 (Polychromatic418967fa.accept_17_9_11_3_1_2353 9 62 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 224 2 4 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 224 (accept_3_2 7 62 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 224 2 3 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 62 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 224 2 2 31 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3
  62 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 224 2 1 31 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 224 (accept_3_2 1 62
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 224 (allA_of_3_0 61 61 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 224 (allA_succ_of_accept 59 60 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 224 2 29 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 60 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 60 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 224 4 14 15 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 224 (accept_3_2 55 60 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 224 2 27 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 224
  (Polychromatic418967fa.accept_21_11_18_14_1_5646 53 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 60 224 4 13 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 60 224 (Polychromatic418967fa.accept_21_9_18_14_1_5648 51 60 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 224 2 25 30 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 224 (accept_3_2 49 60 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 224 4 12 15 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 60 224 2 23 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 60 224 (Polychromatic418967fa.accept_17_11_9_3_1_1463 45 60 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 224 4 11 15 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 224 (accept_3_2 43 60 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 224 2 21 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 41
  60 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 224 4 10 15 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 60 224 2 19 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 60 224 (accept_3_2 37 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 224 4 9 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 60 224 (Polychromatic418967fa.accept_13_9_8_3_1_3045 35 60 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 224 2 17 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 224 (Polychromatic418967fa.accept_13_7_8_3_1_1533
  33 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 224 4 8 15 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 224 (accept_3_2 31
  60 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 224 2 15 30 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 60 224 4 7 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 60 224 (Polychromatic418967fa.accept_17_10_9_3_1_7144 27 60 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 224 2 13 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 224 (accept_3_2 25 60 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 224 4 6 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 60 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 60 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 224 2 11 30 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 224 4 5 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 224 (accept_3_2 19 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  224 2 9 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 224 (Polychromatic418967fa.accept_19_17_3_15_1_9284 17 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 224 4 4 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 224 (Polychromatic418967fa.accept_21_15_18_14_1_5632 15 60 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 224 2 7 30 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 224 (accept_3_2 13 60 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 224 4 3 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 11
  60 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 224 2 5 30 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 224
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 224 4 2 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 224 (accept_3_2 7 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 224
  2 3 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60
  224 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 60 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 224 4 1 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 60 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 224 2 1 30 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 224 (accept_3_2 1 60 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 224
  (allA_succ_of_accept 58 59 224 (accept_3_2 58 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 224 (accept_3_2 55 59 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 224 (Polychromatic418967fa.accept_20_14_19_4_1_7534 54 59 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 224
  (Polychromatic418967fa.accept_10_3_9_4_1_960 53 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 224 (accept_3_2 52 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 59 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 224 (accept_3_2 49 59 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 59 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 224 (accept_3_2 46 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 224 (Polychromatic418967fa.accept_19_6_2_15_1_9266 44 59 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 224 (accept_3_2 43 59 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 224
  (Polychromatic418967fa.accept_21_20_17_14_1_10489 41 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 59 224 (accept_3_2 40 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 59 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 224 (accept_3_2 37 59 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 224 (Polychromatic418967fa.accept_13_10_7_3_1_3041
  36 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 224
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 224 (accept_3_2 34 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 224 (Polychromatic418967fa.accept_18_14_5_8_1_1880 32 59 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 224 (accept_3_2 31 59 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 59 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 224 (accept_3_2 28 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 59 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 224 (accept_3_2 25 59 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 224
  (Polychromatic418967fa.accept_10_3_9_4_1_960 23 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 224 (accept_3_2 22 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 59 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 224 (accept_3_2 19 59 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 59 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 224
  (Polychromatic418967fa.accept_13_4_7_3_1_92 17 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 224 (accept_3_2 16 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 59 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 224 (accept_3_2 13 59 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 59 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 224 (accept_3_2 10 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 59 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 224 (accept_3_2 7 59 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 59 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 224
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 224 (accept_3_2 4 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 59 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 224 (accept_3_2 1 59 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 224 (allA_of_3_0
  58 58 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 224 (allA_succ_of_accept 56 57 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 224 (accept_3_2 55 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 224 (accept_3_2 52 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 57 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 224 (accept_3_2 49 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 224 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 224 (accept_3_2 46 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 224 (Polychromatic418967fa.accept_13_6_5_3_1_426 45 57 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 224
  (Polychromatic418967fa.accept_23_21_11_17_1_13332 44 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 57 224 (accept_3_2 43 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 57 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 224 (accept_3_2 40 57 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703
  39 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 224 (accept_3_2 37 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 224 (Polychromatic418967fa.accept_22_14_13_4_1_8640 36 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 224 (accept_3_2 34 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 57 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 224 (accept_3_2 31 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 224 (accept_3_2 28 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 224 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 57 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 224
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 57 224 (accept_3_2 25 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 57 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 224 (accept_3_2 22 57 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 224 (Polychromatic418967fa.accept_10_1_7_4_1_968
  21 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 224 (accept_3_2 19 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 224 (accept_3_2 16 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 224 (accept_3_2 13 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 224 (accept_3_2 10 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 224 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 57 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 224
  (Polychromatic418967fa.accept_13_8_5_3_1_427 8 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 224 (accept_3_2 7 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  224 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 224 (accept_3_2 4 57 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 57 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  57 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 224 (accept_3_2 1 57 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 224 (allA_succ_of_accept 55 56 224 (accept_3_2 55 56 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 224 2 27 28 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 56 224 (Polychromatic418967fa.accept_13_1_4_3_1_1545 53 56 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 224 4 13 14 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 56 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 56 224 2 25 28 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 56 224 7 7 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 56 224 8 6 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 56 224 (Polychromatic418967fa.accept_19_9_18_15_1_3715 47 56 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 224 2 23 28 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 56 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 56 224 4 11 14 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 56 224 (accept_3_2 43 56 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56
  224 14 3 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  56 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 56 224 8 5 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 56 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 56 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 224 2 19 28 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 224 (accept_3_2 37 56 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 224 4 9 14 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 56 224 7 5 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 56 224 2 17 28 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 33
  56 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 224 8 4 7 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 224 (accept_3_2 31
  56 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 224 2 15 28 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 224
  (Polychromatic418967fa.accept_23_6_10_17_1_13331 29 56 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 224 28 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 56 224 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 56 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 224 2 13 28 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 224 (accept_3_2 25 56 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 224 8 3 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 224 2 11 28 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 56 224 7 3 8 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 56 224 4 5 14 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 224 (accept_3_2 19
  56 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 224 2 9 28 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 56 224
  (Polychromatic418967fa.accept_18_17_2_8_1_6800 17 56 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 56 224 8 2 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 56 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 56 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 224 14 1 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 224 (accept_3_2 13 56 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 56 224 4 3 14 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 56 224 (Polychromatic418967fa.accept_22_11_12_4_1_8675 11 56 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 224 2 5 28 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 224
  (Polychromatic418967fa.accept_19_9_18_15_1_3715 9 56 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 224 8 1 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 56 224 7 1 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 56 224 2 3 28 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 56 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 224 4 1 14 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 56 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 224 2 1 28 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 224 (accept_3_2 1 56 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 224))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 224 (allA_of_3_0 55 55 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 224
  (allA_succ_of_accept 53 54 224 (Polychromatic418967fa.accept_13_1_2_3_1_911 53 54 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 224 2 26 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 51
  54 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 224 2 25 27 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 224 (accept_3_2 49
  54 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 224 2 24 27 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 224
  (Polychromatic418967fa.accept_21_5_12_14_1_7241 47 54 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 224 2 23 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 54 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 54 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 224 2 22 27 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 224 (accept_3_2 43 54 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 224 2 21 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 224 (Polychromatic418967fa.accept_19_3_16_15_1_9281
  41 54 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 224 2 20 27 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 54 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 224 2 19 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 54 224 (accept_3_2 37 54 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 224 2 18 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 224 (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 54 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 224 2 17 27 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 224 2 16 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 54 224 (accept_3_2 31 54 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 224 2 15 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 224 (Polychromatic418967fa.accept_20_9_14_4_1_4540 29 54 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 224 2 14 27 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 224
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 54 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 224 2 13 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 54 224 (accept_3_2 25 54 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 224 2 12 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 224 (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 54 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 224 2 11 27 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 224 2 10 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 54 224 (accept_3_2 19 54 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 224 2 9 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 224 (Polychromatic418967fa.accept_22_17_10_4_1_13330 17 54 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 224 2 8 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  54 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 224 2 7 27 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 224 (accept_3_2 13
  54 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 224 2 6 27 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 224
  (Polychromatic418967fa.accept_13_11_2_3_1_883 11 54 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 224 2 5 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 54 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 54 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 224 2 4 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 224 (accept_3_2 7 54 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 54 224 2 3 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 54 224 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 54 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 224 2 2 27 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  54 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 224 2 1 27 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 224 (accept_3_2 1 54
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 224))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 224 (allA_succ_of_accept 52 53 224 (accept_3_2 52 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 53 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 224 (accept_3_2 49 53 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 224 (Polychromatic418967fa.accept_17_14_2_3_1_7172
  48 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 224
  (Polychromatic418967fa.accept_10_7_3_4_1_978 47 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 224 (accept_3_2 46 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 224 (Polychromatic418967fa.accept_13_5_1_3_1_878 44 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 224 (accept_3_2 43 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 224 (Polychromatic418967fa.accept_22_20_9_4_1_5322 42 53 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 224
  (Polychromatic418967fa.accept_13_2_1_3_1_419 41 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 224 (accept_3_2 40 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 224 (accept_3_2 37 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 224 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 53 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 224
  (Polychromatic418967fa.accept_11_2_9_4_1_310 35 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 224 (accept_3_2 34 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 224 (Polychromatic418967fa.accept_13_6_1_3_1_1522 32 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 224 (accept_3_2 31 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 224 (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 53 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 224
  (Polychromatic418967fa.accept_10_9_3_4_1_985 29 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 224 (accept_3_2 28 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 224 (accept_3_2 25 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 224 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 53 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 224
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 224 (accept_3_2 22 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 224 (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 224 (accept_3_2 19 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 224 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 53 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 224
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 224 (accept_3_2 16 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 224 (accept_3_2 13 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 224 (Polychromatic418967fa.accept_21_12_11_14_1_7239 12 53 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 224
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 224 (accept_3_2 10 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 224 (Polychromatic418967fa.accept_21_8_11_14_1_5665 8 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 224 (accept_3_2 7 53 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 224 (Polychromatic418967fa.accept_13_6_1_3_1_1522 6 53 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 224
  (Polychromatic418967fa.accept_13_5_1_3_1_878 5 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 224 (accept_3_2 4 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 224 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 53 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 224 (accept_3_2 1 53 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 224))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 224 (allA_of_3_0 52 52
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 224 (allA_succ_of_accept 50 51 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 224 (accept_3_2 49 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 224 (accept_3_2 46 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 51 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 224
  (Polychromatic418967fa.accept_19_6_13_15_1_2406 44 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 224 (accept_3_2 43 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 224 (accept_3_2 40 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 51 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 224 (accept_3_2 37 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 224 (accept_3_2 34 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 224 (Polychromatic418967fa.accept_19_14_13_15_1_2532 33 51 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 224 (accept_3_2 31 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 224 (accept_3_2 28 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 51 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 224
  (Polychromatic418967fa.accept_19_7_13_15_1_2407 26 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 224 (accept_3_2 25 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 224 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 224 (accept_3_2 22 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 224 (accept_3_2 19 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 224 (accept_3_2 16 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 51 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 224 (accept_3_2 13 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 224 (accept_3_2 10 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 224 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 51 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 224
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 224 (accept_3_2 7 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  224 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 224 (accept_3_2 4 51 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 51 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  51 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 224 (accept_3_2 1 51 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 224)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 224 (allA_succ_of_accept 49 50 224 (accept_3_2 49 50 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 224 2 24 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 50 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 50 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 224 2 23 25 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 224
  (Polychromatic418967fa.accept_19_7_12_15_1_13329 45 50 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 50 224 2 22 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 50 224 (accept_3_2 43 50 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 50 224 2 21 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 50 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 50 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 224 2 20 25 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 50 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 224 2 19 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 50 224 (accept_3_2 37 50 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 50 224 2 18 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 50 224 (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 50 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 224 2 17 25 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 50 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 224 2 16 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 50 224 (accept_3_2 31 50 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 50 224 2 15 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 224 2 14 25 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 224
  (Polychromatic418967fa.accept_13_1_11_3_1_901 27 50 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 50 224 2 13 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 50 224 (accept_3_2 25 50 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 50 224 2 12 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 50 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 224 2 11 25 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 50 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 224 2 10 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 224 (accept_3_2 19 50 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 50 224 2 9 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 50 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 50 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 224 2 8 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  50 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 224 2 7 25 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 224 (accept_3_2 13
  50 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 224 2 6 25 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 50 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 224 2 5 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 224 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 50 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 224 2 4 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 224 (accept_3_2 7 50 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 224 2 3 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 50 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 224 2 2 25 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 50
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 224 2 1 25 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 224 (accept_3_2 1 50
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 224))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 224 (allA_of_3_0 49 49 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 224
  (allA_succ_of_accept 47 48 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 48 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 224 2 23 24 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 224 (Polychromatic418967fa.accept_13_6_9_3_1_915 45
  48 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 224 4 11 12 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 224 (accept_3_2 43
  48 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 224 2 21 24 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 224 8 5 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 48 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 48 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 224 2 19 24 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 224 (accept_3_2 37 48 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 224 4 9 12 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 48 224 (Polychromatic418967fa.accept_25_10_23_24_1_13328 35 48 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 224 2 17 24 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 224 16 2 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 224 (accept_3_2 31 48 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48
  224 2 15 24 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 48 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 48 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 224 4 7 12 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 224 (Polychromatic418967fa.accept_29_27_19_21_1_13327 27 48 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 224 2 13 24 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 224 (accept_3_2 25 48 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 224 8 3 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 23
  48 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 224 2 11 24 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 224
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 48 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 224 4 5 12 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 224 (accept_3_2 19 48 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  224 2 9 24 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 224 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 48 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 224 16 1 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 48 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 224 2 7 24 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 224 (accept_3_2 13 48 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 224 4 3 12 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 48 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 224 2 5 24 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 48 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 224 8 1 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 224 (accept_3_2 7 48 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 224
  2 3 24 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  224 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 224 4 1 12 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 48 224 (Polychromatic418967fa.accept_18_3_12_8_1_5415 3 48 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 224 2 1 24 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 224 (accept_3_2 1 48 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 224)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 224 (allA_succ_of_accept 46
  47 224 (accept_3_2 46 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 224 (Polychromatic418967fa.accept_13_5_8_3_1_1535 44 47 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 224 (accept_3_2 43 47 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 41
  47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 224 (accept_3_2 40 47
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 224 (Polychromatic418967fa.accept_6_3_5_2_1_12
  39 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 224 (accept_3_2 37 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 224 (Polychromatic418967fa.accept_21_15_5_14_1_11856 36 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 224 (Polychromatic418967fa.accept_13_9_8_3_1_3045 35 47 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 224 (accept_3_2 34 47 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 224 (accept_3_2 31 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 47 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 224 (accept_3_2 28 47 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 224 (accept_3_2 25 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 224 (accept_3_2 22 47 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 224
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 224 (accept_3_2 19 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 224 (Polychromatic418967fa.accept_20_17_7_4_1_7671 17 47 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 224 (accept_3_2 16 47 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 224 (accept_3_2 13 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 47 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 224 (accept_3_2 10 47 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 224
  (Polychromatic418967fa.accept_17_8_13_3_1_3432 8 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 224 (accept_3_2 7 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  224 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 47 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 224 (accept_3_2 4 47 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  47 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 224 (accept_3_2 1 47 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 224))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  224 (allA_of_3_0 46 46 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 224 (allA_succ_of_accept 44 45 224
  (Polychromatic418967fa.accept_13_5_6_3_1_868 44 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 224 (accept_3_2 43 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 224 (accept_3_2 40 45 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 45 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 224
  (Polychromatic418967fa.accept_21_17_3_14_1_2807 38 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 224 (accept_3_2 37 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 224 (accept_3_2 34 45 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 224 (Polychromatic418967fa.accept_19_14_7_15_1_3732 33 45 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 224
  (Polychromatic418967fa.accept_19_13_7_15_1_5054 32 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 224 (accept_3_2 31 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 224 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 224 (accept_3_2 28 45 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 224 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 45 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 224
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 224 (accept_3_2 25 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 224 (Polychromatic418967fa.accept_18_6_9_8_1_6812 24 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 224 (accept_3_2 22 45 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 224 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 45 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 224
  (Polychromatic418967fa.accept_23_20_22_17_1_13326 20 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 45 224 (accept_3_2 19 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 45 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 224 (accept_3_2 16 45 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 224 (Polychromatic418967fa.accept_20_15_5_4_1_4566
  15 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 224
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 14 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 224 (accept_3_2 13 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 224 (Polychromatic418967fa.accept_19_12_7_15_1_3731 12 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 224 (accept_3_2 10 45 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 45 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 224
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 224 (accept_3_2 7 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  224 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 224 (accept_3_2 4 45 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 224 (Polychromatic418967fa.accept_18_3_9_8_1_2977 3 45 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 224 (Polychromatic418967fa.accept_17_2_11_3_1_4654
  2 45 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 224 (accept_3_2 1 45
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 224))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  44 224 (allA_succ_of_accept 43 44 224 (accept_3_2 43 44 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  42 44 224 2 21 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 44 224 (Polychromatic418967fa.accept_13_2_5_3_1_406 41 44 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 224 4 10 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 224
  (Polychromatic418967fa.accept_24_15_20_8_1_13325 39 44 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 44 224 2 19 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 44 224 (accept_3_2 37 44 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 44 224 4 9 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 44 224 (Polychromatic418967fa.accept_13_9_5_3_1_428 35 44 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 224 2 17 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 224
  (Polychromatic418967fa.accept_21_12_2_14_1_10513 33 44 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 44 224 4 8 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 44 224 (accept_3_2 31 44 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 44 224 2 15 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 44 224 (Polychromatic418967fa.accept_19_10_6_15_1_6444 29 44 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 224 4 7 11 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 224
  (Polychromatic418967fa.accept_13_1_5_3_1_888 27 44 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 224 2 13 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 44 224 (accept_3_2 25 44 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 44 224 4 6 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 44 224 (Polychromatic418967fa.accept_19_4_6_15_1_7916 23 44 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 224 2 11 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 224 (Polychromatic418967fa.accept_13_8_5_3_1_427 21
  44 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 224 4 5 11 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 224 (accept_3_2 19
  44 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 224 2 9 22 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 224
  (Polychromatic418967fa.accept_21_17_2_14_1_7208 17 44 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 44 224 4 4 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 44 224 (Polychromatic418967fa.accept_13_2_5_3_1_406 15 44 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 224 2 7 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 224 (accept_3_2 13 44 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 224 4 3 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 44 224 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 44 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 224 2 5 22 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 224
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 44 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 224 4 2 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 224 (accept_3_2 7 44 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 224
  2 3 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  224 (Polychromatic418967fa.accept_19_5_6_15_1_10686 5 44 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 44 224 4 1 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 44 224 (Polychromatic418967fa.accept_21_3_2_14_1_7235 3 44 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 224 2 1 22 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 224 (accept_3_2 1 44 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 44 224)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 224 (allA_of_3_0 43 43
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 224 (allA_succ_of_accept 41 42 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 224 2 20 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 42 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 224 2 19 21 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 224 (accept_3_2 37 42 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 224 2 18 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 42 224 7 5 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 42 224 2 17 21 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 224 2 16 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 224 (accept_3_2 31 42 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 224 2 15 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 42 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 224 14 2 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 27
  42 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 224 2 13 21 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 224 (accept_3_2 25
  42 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 224 2 12 21 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 224 2 11 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 42 224 7 3 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 42 224 2 10 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 42 224 (accept_3_2 19 42 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 224 2 9 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 42 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 224 2 8 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  42 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 224 14 1 3 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 224 (accept_3_2 13
  42 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 224 2 6 21 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 224 2 5 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 42 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 224 2 4 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 42 224 7 1 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 224 2 3 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 224 2 2 21 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 42 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 42 224 2 1 21 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 224 (accept_3_2 1 42 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  224)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 224 (allA_succ_of_accept 40 41 224 (accept_3_2 40 41 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39
  41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 224 (accept_3_2 37 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 224 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 41 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 224 (accept_3_2 34 41 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 224
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 32 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 224 (accept_3_2 31 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 41 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 224 (accept_3_2 28 41 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 224 (accept_3_2 25 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 224 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 41 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 224 (accept_3_2 22 41 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 224 (accept_3_2 19 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 41 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 224 (accept_3_2 16 41 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 224 (accept_3_2 13 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 41 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 224 (accept_3_2 10 41 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 224
  (Polychromatic418967fa.accept_19_8_3_15_1_2510 8 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 224 (accept_3_2 7 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  224 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 41 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 224 (accept_3_2 4 41 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 41
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 224 (accept_3_2 1 41 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 224))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 224
  (allA_of_3_0 40 40 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 224 (allA_succ_of_accept 38 39 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 224 (accept_3_2 37 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 224 (accept_3_2 34 39 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 39 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 224 (accept_3_2 31 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 224 (accept_3_2 28 39 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 224 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 39 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 224
  (Polychromatic418967fa.accept_21_5_18_14_1_2793 26 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 224 (accept_3_2 25 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 224 (accept_3_2 22 39 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 39 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 224 (accept_3_2 19 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 224 (accept_3_2 16 39 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 224 (accept_3_2 13 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 224 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 224 (accept_3_2 10 39 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 224 (Polychromatic418967fa.accept_18_9_3_8_1_5419 9 39 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 224
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 224 (accept_3_2 7 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  224 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 224 (accept_3_2 4 39 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 39 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  39 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 224 (accept_3_2 1 39 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 224))))))))))))))))))))))))))))))))))))))) (allB_succ 38 224
  (allA_succ_of_accept 37 38 224 (accept_3_2 37 38 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  224 2 18 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 38 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 38 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 224 2 17 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 38 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 224 2 16 19 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 224 (accept_3_2 31 38 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 224 2 15 19 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 29 38 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 224 2 14 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 38 224 (Polychromatic418967fa.accept_25_2_13_24_1_13324 27 38 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 224 2 13 19 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 224 (accept_3_2 25 38 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 224 2 12 19 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 38 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 38 224 2 11 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 38 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 38 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 224 2 10 19 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 224 (accept_3_2 19 38 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38 224 2 9 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 38 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 17
  38 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 224 2 8 19 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 38 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 38 224 2 7 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 38 224 (accept_3_2 13 38 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38
  224 2 6 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  38 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 38 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 38 224 2 5 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 38 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 38 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 224 2 4 19 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 224 (accept_3_2 7 38 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 224 2 3 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 38 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 224 2 2 19 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 38 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 38 224 2 1 19 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 38 224 (accept_3_2 1 38 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  224)))))))))))))))))))))))))))))))))))))) (allB_succ 37 224 (allA_of_3_0 37 37 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 36 224 (allA_succ_of_accept 35 36 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 36 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 224 2 17 18 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 224
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 33 36 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 224 4 8 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 224 (accept_3_2 31 36 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36
  224 2 15 18 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 36 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 36 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 36 224 4 7 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 36 224 (Polychromatic418967fa.accept_19_8_17_15_1_11952 27 36 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 224 2 13 18 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 224 (accept_3_2 25 36 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 224 4 6 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 224 (Polychromatic418967fa.accept_15_8_6_14_1_975
  23 36 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 224 2 11 18 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 224
  (Polychromatic418967fa.accept_19_2_17_15_1_1377 21 36 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 36 224 4 5 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 36 224 (accept_3_2 19 36 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36
  224 2 9 18 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  36 224 (Polychromatic418967fa.accept_21_17_15_14_1_5707 17 36 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 36 224 4 4 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 36 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 36 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 224 2 7 18 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 224 (accept_3_2 13 36 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 224 4 3 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 224 (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 36
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 224 2 5 18 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 224
  (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 36 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 224 4 2 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 224 (accept_3_2 7 36 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 224
  2 3 18 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36
  224 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 36 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 36 224 4 1 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 36 224 (Polychromatic418967fa.accept_19_3_17_15_1_6459 3 36 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 224 2 1 18 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 224 (accept_3_2 1 36 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 224)))))))))))))))))))))))))))))))))))) (allB_succ 35 224 (allA_succ_of_accept 34 35 224
  (accept_3_2 34 35 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 35 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 224 (Polychromatic418967fa.accept_13_6_9_3_1_915 32 35 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 224 (accept_3_2 31 35 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 224 (Polychromatic418967fa.accept_19_11_16_15_1_11951 30 35 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 224
  (Polychromatic418967fa.accept_10_9_5_4_1_966 29 35 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 35 224 7 4 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 35 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 35 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 224 (accept_3_2 25 35 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 224 (Polychromatic418967fa.accept_15_9_5_14_1_973
  24 35 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 224
  (Polychromatic418967fa.accept_15_8_5_14_1_986 23 35 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 224 (accept_3_2 22 35 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35
  224 7 3 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  35 224 (Polychromatic418967fa.accept_11_9_2_4_1_707 20 35 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 35 224 (accept_3_2 19 35 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 35 224 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 35 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 35 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 224 (accept_3_2 16 35 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  35 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 35 224 7 2 5 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 35 224 (accept_3_2 13
  35 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 224
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 35 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 35 224 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 35 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 224 (accept_3_2 10 35 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 35 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 224 (Polychromatic418967fa.accept_13_8_9_3_1_2213 8
  35 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 35 224 7 1 5 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 35 224
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 35 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 224 (Polychromatic418967fa.accept_13_5_9_3_1_870 5 35 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 224 (accept_3_2 4 35 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  35 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 224 (accept_3_2 1 35 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 224))))))))))))))))))))))))))))))))))) (allB_succ 34 224
  (allA_of_3_0 34 34 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 224 (allA_succ_of_accept 32 33 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 224 (accept_3_2 31 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 224 (accept_3_2 28 33 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 33 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 224
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 224 (accept_3_2 25 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 224 (Polychromatic418967fa.accept_13_11_7_3_1_894 24 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 224 (accept_3_2 22 33 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 224 (accept_3_2 19 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 224 (accept_3_2 16 33 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 224 (Polychromatic418967fa.accept_21_15_12_14_1_7232 15 33 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 224 (accept_3_2 13 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 224 (accept_3_2 10 33 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 33 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 224
  (Polychromatic418967fa.accept_13_8_7_3_1_430 8 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 224 (accept_3_2 7 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  224 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 33 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 224 (accept_3_2 4 33 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 33 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  33 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 224 (accept_3_2 1 33 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 224))))))))))))))))))))))))))))))))) (allB_succ 32 224
  (allA_succ_of_accept 31 32 224 (accept_3_2 31 32 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  224 2 15 16 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 32 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 224 4 7 8 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 32 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 224 2 13 16 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 224 (accept_3_2 25 32 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 224 8 3 4 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 224 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 32 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 224 2 11 16 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 32 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 224 4 5 8 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 224 (accept_3_2 19 32 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  224 2 9 16 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 32 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 224 16 1 2 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 32 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 224 2 7 16 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 224 (accept_3_2 13 32 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 224 4 3 8 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 32 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 224 2 5 16 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 224
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 32 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 224 8 1 4 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 224 (accept_3_2 7 32 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 224
  2 3 16 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  224 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 32 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 32 224 4 1 8 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 32 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 32 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 224 2 1 16 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 224 (accept_3_2 1 32 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 32 224)))))))))))))))))))))))))))))))) (allB_succ 31 224 (allA_of_3_0 31 31 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 224 (allA_succ_of_accept 29 30 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 30 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 224 2 14 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 30 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 30 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 224 2 13 15 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 224 (accept_3_2 25 30 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 224 2 12 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 23
  30 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 224 2 11 15 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 224 2 10 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 224 (accept_3_2 19 30 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 224 2 9 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 224 (Polychromatic418967fa.accept_21_17_9_14_1_5700 17 30 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 224 2 8 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  30 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 224 2 7 15 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 224 (accept_3_2 13
  30 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 224 2 6 15 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 30 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 224 2 5 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 224 2 4 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 224 (accept_3_2 7 30 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 30 224 2 3 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 30 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 30 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 224 2 2 15 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  30 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 224 2 1 15 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 224 (accept_3_2 1 30
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 224)))))))))))))))))))))))))))))) (allB_succ 29 224
  (allA_succ_of_accept 28 29 224 (accept_3_2 28 29 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  29 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 29 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 224 (accept_3_2 25 29 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 29 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 29 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 224 (accept_3_2 22 29 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 224 (Polychromatic418967fa.accept_25_20_4_24_1_13323 20 29 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 224 (accept_3_2 19 29 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 29 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 224
  (Polychromatic418967fa.accept_19_17_10_15_1_7927 17 29 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 29 224 (accept_3_2 16 29 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 29 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 224 (accept_3_2 13 29 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 12
  29 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 224
  (Polychromatic418967fa.accept_19_11_10_15_1_3741 11 29 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 29 224 (accept_3_2 10 29 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 29 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 29 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 224 (accept_3_2 7 29 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  29 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 29 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 224 (accept_3_2 4 29 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 29 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 224 (accept_3_2 1 29 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 224))))))))))))))))))))))))))))) (allB_succ 28 224 (allA_of_3_0 28 28 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 224 (allA_succ_of_accept 26 27 224 (Polychromatic418967fa.accept_15_11_12_14_1_2612
  26 27 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 224 (accept_3_2 25
  27 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 224
  (Polychromatic418967fa.accept_13_11_1_3_1_910 24 27 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 224 (accept_3_2 22 27 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 27 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 224 (Polychromatic418967fa.accept_13_7_1_3_1_1523
  20 27 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 224 (accept_3_2 19
  27 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 224
  (Polychromatic418967fa.accept_12_6_3_8_1_512 18 27 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 224 (accept_3_2 16 27 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 224 (Polychromatic418967fa.accept_13_2_1_3_1_419 15 27 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 224
  (Polychromatic418967fa.accept_23_14_4_17_1_13322 14 27 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 27 224 (accept_3_2 13 27 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 27 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 27 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 224 (accept_3_2 10 27 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 224 (Polychromatic418967fa.accept_15_9_12_14_1_963
  9 27 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 224
  (Polychromatic418967fa.accept_21_8_6_14_1_4184 8 27 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 224 (accept_3_2 7 27 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  224 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 27 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 224 (accept_3_2 4 27 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 27 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  27 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 224 (accept_3_2 1 27 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 224))))))))))))))))))))))))))) (allB_succ 26 224
  (allA_succ_of_accept 25 26 224 (accept_3_2 25 26 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  224 2 12 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 26 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 26 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 224 2 11 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 224 (Polychromatic418967fa.accept_27_21_26_8_1_13321 21 26 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 224 2 10 13 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 224 (accept_3_2 19 26 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 224 2 9 13 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 224
  (Polychromatic418967fa.accept_12_5_2_8_1_172 17 26 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 26 224 2 8 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 26 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 26 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 224 2 7 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 224 (accept_3_2 13 26 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 224 2 6 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 26 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 224 2 5 13 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 224
  (Polychromatic418967fa.accept_21_9_5_14_1_1568 9 26 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 26 224 2 4 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 26 224 (accept_3_2 7 26 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 224
  2 3 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26
  224 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 26 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 26 224 2 2 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 26 224 (Polychromatic418967fa.accept_15_3_11_14_1_1705 3 26 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 224 2 1 13 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 224 (accept_3_2 1 26 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 224)))))))))))))))))))))))))) (allB_succ 25 224 (allA_of_3_0 25 25 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 224 (allA_succ_of_accept 23 24 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 23
  24 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 224 2 11 12 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 224 4 5 6 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 224 (accept_3_2 19 24 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  224 2 9 12 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 24 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 224 8 2 3 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 224 (Polychromatic418967fa.accept_13_2_11_3_1_873 15 24 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 224 2 7 12 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 224 (accept_3_2 13 24 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 224 4 3 6 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 224 2 5 12 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 224
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 24 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 224 8 1 3 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 224 (accept_3_2 7 24 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 224
  2 3 12 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  224 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 224 4 1 6 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 224 2 1 12 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 224 (accept_3_2 1 24 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 224)))))))))))))))))))))))) (allB_succ 23 224 (allA_succ_of_accept 22 23 224 (accept_3_2 22
  23 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 23 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 224 (accept_3_2 19 23 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 224 (Polychromatic418967fa.accept_17_1_6_3_1_4700 18 23 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 224 (Polychromatic418967fa.accept_10_7_3_4_1_978
  17 23 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 224 (accept_3_2 16
  23 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 23 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 224 (accept_3_2 13 23 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 23 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11
  23 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 224 (accept_3_2 10 23
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 224 (Polychromatic418967fa.accept_6_3_5_2_1_12
  9 23 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 224
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 23 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 224 (accept_3_2 7 23 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  224 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 23 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 224 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 23 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 224 (accept_3_2 4 23 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 224 (accept_3_2 1 23 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 224))))))))))))))))))))))) (allB_succ 22 224 (allA_of_3_0 22 22
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 224 (allA_succ_of_accept 20 21 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 21 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 224 (accept_3_2 19 21 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 21 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 224 (accept_3_2 16 21 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 21 224 7 2 3 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 21 224 (accept_3_2 13 21 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 224 (Polychromatic418967fa.accept_18_12_3_8_1_6817 12 21
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 224 (accept_3_2 10 21 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 224 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 21 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 224 (Polychromatic418967fa.accept_15_8_6_14_1_975 8 21 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 224 7 1 3 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 21 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 224 (accept_3_2 4 21 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  224 (Polychromatic418967fa.accept_20_3_1_4_1_7654 3 21 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 21 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 224 (accept_3_2 1 21 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 224))))))))))))))))))))) (allB_succ 20 224 (allA_succ_of_accept 19 20 224
  (accept_3_2 19 20 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 224 2 9 10 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 224
  (Polychromatic418967fa.accept_13_4_7_3_1_92 17 20 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 224 4 4 5 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 20 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 224 2 7 10 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 224 (accept_3_2 13 20 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 224 4 3 5 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 20 224 (Polychromatic418967fa.accept_13_11_7_3_1_894 11 20 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 224 2 5 10 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 224
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 20 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 224 4 2 5 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 224 (accept_3_2 7 20 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 224
  2 3 10 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 20 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 224 4 1 5 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 20 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 224 2 1 10 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 224 (accept_3_2 1 20 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 224)))))))))))))))))))) (allB_succ 19 224 (allA_of_3_0 19 19 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 224 (allA_succ_of_accept 17 18 224 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 18 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 224 2 8 9 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 18 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 224 2 7 9 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 224 (accept_3_2 13 18 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  224 2 6 9 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 224 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 18 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 224 2 5 9 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 18 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 224 2 4 9 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 224 (accept_3_2 7 18 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 224 2 3 9 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 224 (Polychromatic418967fa.accept_21_5_18_14_1_2793 5 18 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 224 2 2 9 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 224
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 18 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 224 2 1 9 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 224 (accept_3_2 1 18 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  224)))))))))))))))))) (allB_succ 17 224 (allA_succ_of_accept 16 17 224 (accept_3_2 16 17 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 17 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 224 (accept_3_2 13 17 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 17 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 17 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 224 (accept_3_2 10 17 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 224
  (Polychromatic418967fa.accept_19_8_17_15_1_11952 8 17 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 224 (accept_3_2 7 17 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  224 (Polychromatic418967fa.accept_22_6_17_4_1_11783 6 17 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 224 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 17 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 224 (accept_3_2 4 17 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 17 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 224 (accept_3_2 1 17 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  224))))))))))))))))) (allB_succ 16 224 (allA_of_3_0 16 16 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15
  224 (allA_succ_of_accept 14 15 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 15 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 224 (accept_3_2 13 15 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 15 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  15 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 224 (accept_3_2 10 15
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 224
  (Polychromatic418967fa.accept_10_9_5_4_1_966 9 15 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 224 (Polychromatic418967fa.accept_21_8_15_14_1_4176 8 15 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 224 (accept_3_2 7 15 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 15 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 224 (accept_3_2 4 15 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  15 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 15 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 224 (accept_3_2 1 15 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  224))))))))))))))) (allB_succ 14 224 (allA_succ_of_accept 13 14 224 (accept_3_2 13 14 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 14 224 2 6 7 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 14 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 14 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 224 2 5 7 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 224 (Polychromatic418967fa.accept_20_9_14_4_1_4540 9
  14 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 224 2 4 7 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 14 224 7 1 2 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 14 224 2 3 7 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 224
  (Polychromatic418967fa.accept_12_5_2_8_1_172 5 14 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 224 2 2 7 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 14 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 224 2 1 7 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 224 (accept_3_2 1 14 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 224)))))))))))))) (allB_succ 13 224 (allA_of_3_0 13 13 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 224 (allA_succ_of_accept 11 12 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 12 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 224 2 5 6 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 224
  (Polychromatic418967fa.accept_13_9_12_3_1_907 9 12 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 224 4 2 3 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 224 (accept_3_2 7 12 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 224
  2 3 6 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12
  224 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 224 4 1 3 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 12 224 (Polychromatic418967fa.accept_18_3_12_8_1_5415 3 12 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 224 2 1 6 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 224 (accept_3_2 1 12 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 224)))))))))))) (allB_succ 11 224 (allA_succ_of_accept 10 11 224 (accept_3_2 10 11 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 224
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 8 11 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 224 (accept_3_2 7 11 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  224 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 11 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 11 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 224 (accept_3_2 4 11 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  11 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 224 (accept_3_2 1 11 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 224))))))))))) (allB_succ 10 224 (allA_of_3_0 10 10 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 9 224 (allA_succ_of_accept 8 9 224
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 9 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 224 (accept_3_2 7 9 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 224
  (Polychromatic418967fa.accept_12_6_9_8_1_165 6 9 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 224 (accept_3_2 4 9 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 9 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 224 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 9
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 224 (accept_3_2 1 9 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 224))))))))) (allB_succ 8 224 (allA_succ_of_accept 7 8 224
  (accept_3_2 7 8 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 224 2 3 4 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 224
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 8 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 224 4 1 2 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 224 (Polychromatic418967fa.accept_19_3_8_15_1_2523 3 8 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 224 2 1 4 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 224 (accept_3_2 1 8 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 224)))))))) (allB_succ 7 224 (allA_of_3_0 7 7 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 6 224 (allA_succ_of_accept 5 6 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 6 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 224 2 2 3 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 6
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 224 2 1 3 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 224 (accept_3_2 1 6
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 224)))))) (allB_succ 5 224 (allA_succ_of_accept 4 5 224
  (accept_3_2 4 5 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 224 (accept_3_2 1 5 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 224))))) (allB_succ 4 224 (allA_of_3_0 4 4 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 3 224 (allA_succ_of_accept 2 3 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 3 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 224 (accept_3_2 1 3 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 3 224))) (allB_succ 2 224 (allA_succ_of_accept 1 2 224 (accept_3_2 1 2 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 2 224)) (allB_two
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


